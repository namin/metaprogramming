(define env-lookup
  (lambda (env x)
    (if (null? env)
        (error 'env-lookup (format "unbound variable ~a" x))
        (let ((b (assq x (car env))))
          (if b
              (cdr b)
              (env-lookup (cdr env) x))))))

(define make-frame
  (lambda (params args)
    (if (null? params)
        (if (null? args)
            '()
            (error 'make-frame "not same length"))
        (if (null? args)
            (error 'make-frame "not same length")
            (cons (cons (car params) (car args))
                  (make-frame (cdr params) (cdr args)))))))

(define env-extend
  (lambda (env params args)
    (cons (make-frame params args) env)))

(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define evl
  (lambda (exp env)
    (cond
      ((or (number? exp) (boolean? exp) (string? exp))
       exp)
      ((symbol? exp)
       (env-lookup env exp))
      (((tagged? 'quote) exp)
       (cadr exp))
      (((tagged? 'begin) exp)
       (if (null? (cddr exp))
           (evl (cadr exp) env)
           (begin
             (evl (cadr exp) env)
             (evl (cons 'begin (cddr exp)) env))))
      (((tagged? 'let) exp)
       (let ((params (map car (cadr exp)))
             (args (map cadr (cadr exp)))
             (body (cons 'begin (cddr exp))))
         ;; example
         ;; (let ((a 1) (b 2)) (+ a b))
         ;; ==>
         ;; ((lambda (a b) (+ a b) 1 2)
         (let ((t (cons (list 'lambda params body)
                        args)))
           (evl t env))))
      (((tagged? 'define) exp)
       (let ((old-frame (car env))
             (b (cons (cadr exp) 'undefined)))
         (let ((new-frame (cons
                           b
                           old-frame)))
           (set-car! env new-frame)
           (let ((r (evl (caddr exp) env)))
             (set-cdr! b r)
             'undefined))))
      (((tagged? 'if) exp)
       (if (evl (cadr exp) env)
           (evl (caddr exp) env)
           (evl (cadddr exp) env)))
      (((tagged? 'and) exp)
       ;; assumes exactly two arguments
       (evl (list 'if (cadr exp) (caddr exp) #f) env))
      (((tagged? 'or) exp)
       ;; assumes we only care about boolean results
       (if (null? (cdr exp))
           #f
           (evl (list 'if (cadr exp) #t (cons 'or (cddr exp))) env)))
      (((tagged? 'cond) exp)
       (if (null? (cdr exp))
           'undefined
           (let ((clause (cadr exp))
                 (rest (cddr exp)))
             (if (or (eq? 'else (car clause)) (evl (car clause) env))
                 (evl (cadr clause) env)
                 (evl (cons 'cond rest) env)))))
      (((tagged? 'lambda) exp)
       (list 'closure env (cadr exp) (caddr exp)))
      (else ;; application
       (app (evl (car exp) env)
            (map (lambda (e) (evl e env)) (cdr exp)))))))

(define app
  (lambda (p args)
    (cond
      (((tagged? 'closure) p)
       (let ((clo-env (cadr p))
             (params (caddr p))
             (body (cadddr p)))
         (evl body (env-extend clo-env params args))))
      ((procedure? p)
       (apply p args))
      (else
       (error 'apply (format "expected procedure, not ~a" p))))))

(define make-global-frame
  (lambda ()
    (list
     (cons '* *)
     (cons '- -)
     (cons '< <)
     (cons 'list list)
     (cons 'cons cons)
     (cons 'car car)
     (cons 'cdr cdr)
     (cons 'cadr cadr)
     (cons 'cddr cddr)
     (cons 'caddr caddr)
     (cons 'cdddr cdddr)
     (cons 'cadddr cadddr)
     (cons 'null? null?)
     (cons 'pair? pair?)
     (cons 'eq? eq?)
     (cons 'number? number?)
     (cons 'boolean? boolean?)
     (cons 'string? string?)
     (cons 'symbol? symbol?)
     (cons 'apply apply)
     (cons 'error error)
     (cons 'format format)
     (cons 'newline newline)
     (cons 'display display)
     (cons 'assq assq)
     (cons 'map (lambda (f xs) (map (lambda (x) (app f (list x))) xs))))))

(define make-global-env
  (lambda ()
    (cons (make-global-frame) '())))

(define repl
  (lambda ()
    (let ((global-env (make-global-env)))
      (define loop
        (lambda ()
          (newline)
          (let ((val (evl (read) global-env)))
            (display ";==> ")
            (display val)
            (newline))
          (loop)))
      (loop))))
