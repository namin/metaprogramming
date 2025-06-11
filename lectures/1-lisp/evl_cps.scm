(define find-binding
  (lambda (env x)
    (if (null? env)
        #f
        (or (assq x (car env)) (find-binding (cdr env) x)))))

(define env-lookup
  (lambda (env x)
    (let ((b (find-binding env x)))
      (if b
          (cdr b)
          (error 'env-lookup (format "unbound variable ~a" x))))))

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
  (lambda (exp env cont)
    (cond
      ((or (number? exp) (boolean? exp) (string? exp))
       (cont exp))
      ((symbol? exp)
       (cont (env-lookup env exp)))
      (((tagged? 'quote) exp)
       (cont (cadr exp)))
      (((tagged? 'begin) exp)
       (if (null? (cddr exp))
           (evl (cadr exp) env cont)
           (evl (cadr exp) env
                (lambda (v)
                  (evl (cons 'begin (cddr exp)) env cont)))))
      (((tagged? 'let) exp)
       (let ((params (map car (cadr exp)))
             (args (map cadr (cadr exp)))
             (body (cons 'begin (cddr exp))))
         (evl (cons (list 'lambda params body) args) env cont)))
      (((tagged? 'define) exp)
       (let ((old-frame (car env))
             (b (cons (cadr exp) 'undefined)))
         (let ((new-frame (cons b old-frame)))
           (set-car! env new-frame)
           (evl (caddr exp) env
                (lambda (r)
                  (set-cdr! b r)
                  (cont 'undefined))))))
      (((tagged? 'set!) exp)
       (evl (caddr exp) env
            (lambda (val)
              (eval-set! (cadr exp) val env cont))))
      (((tagged? 'if) exp)
       (evl (cadr exp) env
            (lambda (v)
              (if v
                  (evl (caddr exp) env cont)
                  (evl (cadddr exp) env cont)))))
      (((tagged? 'and) exp)
       (if (null? (cdr exp))
           (cont #t)
           (if (null? (cddr exp))
               (evl (cadr exp) env cont)
               (evl (cadr exp) env
                    (lambda (v)
                      (if v
                          (evl (cons 'and (cddr exp)) env cont)
                          (cont #f)))))))
      (((tagged? 'or) exp)
       (if (null? (cdr exp))
           (cont #f)
           (if (null? (cddr exp))
               (evl (cadr exp) env cont)
               (evl (cadr exp) env
                    (lambda (v)
                      (if v
                          (cont v)
                          (evl (cons 'or (cddr exp)) env cont)))))))
      (((tagged? 'cond) exp)
       (if (null? (cdr exp))
           (cont 'undefined)
           (let ((clause (cadr exp))
                 (rest (cddr exp)))
             (if (eq? 'else (car clause))
                 (evl (cadr clause) env cont)
                 (evl (car clause) env
                      (lambda (v)
                        (if v
                            (evl (cadr clause) env cont)
                            (evl (cons 'cond rest) env cont))))))))
      (((tagged? 'lambda) exp)
       (cont (list 'closure env (cadr exp)
                   (if (null? (cdddr exp))
                       (caddr exp)
                       (cons 'begin (cddr exp))))))
      (((tagged? 'load) exp)
       (evl (cadr exp) env
            (lambda (filename)
              (file-load env filename cont))))
      (else ;; application
       (evl (car exp) env
            (lambda (p)
              (evlis (cdr exp) env
                     (lambda (args)
                       (app p args env cont)))))))))

(define eval-set!
  (lambda (var val env cont)
    (let ((binding (find-binding env var)))
      (if binding
          (begin
            (set-cdr! binding val)
            (cont 'undefined))
          (error 'set! "unbound variable" var)))))

(define evlis
  (lambda (exps env cont)
    (if (null? exps)
        (cont '())
        (evl (car exps) env
             (lambda (v)
               (evlis (cdr exps) env
                      (lambda (vs)
                        (cont (cons v vs)))))))))

(define app
  (lambda (p args env cont)
    (cond
      (((tagged? 'closure) p)
       (let ((clo-env (cadr p))
             (params (caddr p))
             (body (cadddr p)))
         (evl body (env-extend clo-env params args) cont)))
      ((procedure? p)
       (cont (apply p args)))

      ;; we hard code higher-order primitives
      ((eq? p 'map-primitive)
       (map-with-context (car args) (cadr args) env cont))
      ((eq? p 'with-exception-handler-primitive)
       (with-exception-handler-with-context (car args) (cadr args) env cont))
      ((eq? p 'call-with-input-file-primitive)
       (call-with-input-file-with-context (car args) (cadr args) env cont))

      (else
       (error 'app (format "expected procedure, not ~a" p))))))

(define map-with-context
  (lambda (f xs env cont)
    (define map-helper
      (lambda (xs acc)
        (if (null? xs)
            (cont (reverse acc))
            (app f (list (car xs)) env
                 (lambda (v)
                   (map-helper (cdr xs) (cons v acc)))))))
    (map-helper xs '())))

(define with-exception-handler-with-context
  (lambda (handler thunk env cont)
    (with-exception-handler
      (lambda (exn)
        (app handler (list exn) env cont))
      (lambda ()
        (app thunk '() env cont)))))

(define call-with-input-file-with-context
  (lambda (filename proc env cont)
    (call-with-input-file
      filename
      (lambda (port)
        (app proc (list port) env cont)))))

(define file-load-iter
  (lambda (env port last-value cont)
    (let ((exp (read port)))
      (if (eof-object? exp)
          (begin
            (newline)
            (cont last-value))
          (begin
            (display ".")
            (evl exp env
                 (lambda (v)
                   (file-load-iter env port v cont))))))))

(define file-load
  (lambda (env filename cont)
    (call-with-input-file filename
      (lambda (port) (file-load-iter env port 'undefined cont)))))

(define make-global-frame
  (lambda ()
    (list
     (cons '+ +)
     (cons '* *)
     (cons '- -)
     (cons '< <)
     (cons '= =)
     (cons 'not not)
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
     (cons 'length length)
     (cons 'reverse reverse)
     (cons 'apply apply)
     (cons 'error error)
     (cons 'format format)
     (cons 'newline newline)
     (cons 'display display)
     (cons 'write write)
     (cons 'print-graph print-graph)
     (cons 'assq assq)
     (cons 'procedure? procedure?)
     (cons 'set-car! set-car!)
     (cons 'set-cdr! set-cdr!)
     (cons 'read read)
     (cons 'display-condition display-condition)
     (cons 'eof-object? eof-object?)
     (cons 'cpu-time cpu-time)
     (cons 'map 'map-primitive)
     (cons 'with-exception-handler 'with-exception-handler-primitive)
     (cons 'call-with-input-file 'call-with-input-file-primitive)
     )))

(define make-global-env
  (lambda ()
    (cons (make-global-frame) '())))

(print-graph #t)
(define *quit* ''eof)

(define repl-loop
  (lambda (evl env level iter)
    (newline) (display level) (display "-") (display iter) (display "> ")
    (let ((exp (read)))
      (cond
        ((eof-object? exp) ;; Ctrl-D → quit this REPL level
         (display ";<eof>\n")
         *quit*)
        (else
         (with-exception-handler
          (lambda (c)
            (display ";Error: ") (display-condition c) (newline)
            (repl-loop evl env level (+ iter 1)))
          (lambda ()
            (let ((start (cpu-time)))
              (let ((v (evl exp env (lambda (v) v))))
                (let ((elapsed (- (cpu-time) start)))
                  (if (eq? v *quit*)
                      *quit*
                      (begin
                        (display ";==> ") (write v)
                        (newline)
                        (display ";(") (display elapsed) (display " cpu-time)")
                        (newline)
                        (repl-loop evl env level (+ iter 1))))))))))))))

(define repl
  (lambda (level)
    (repl-loop evl (make-global-env) level 0)))
