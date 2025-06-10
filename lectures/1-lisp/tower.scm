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

(define make-meta-cont-level
  (lambda (level)
    (let ((upper-env (make-global-env)))
      (cons upper-env
            (lambda (val mc)
              (display (format "Returned to level ~a with: " level))
              (display val)
              (newline)
              (repl-loop evl upper-env mc level 0))))))

(define get-meta-cont
  (lambda (level)
    (cons (make-meta-cont-level level)
          (lambda () (get-meta-cont (+ level 1))))))

(define meta-cont-force
  (lambda (mc)
    (if (procedure? (cdr mc))
        (cons (car mc) ((cdr mc)))
        mc)))

(define evl
  (lambda (exp env cont meta-cont)
    (cond
      ((or (number? exp) (boolean? exp) (string? exp))
       (cont exp meta-cont))
      
      ((symbol? exp)
       (cont (env-lookup env exp) meta-cont))
      
      (((tagged? 'quote) exp)
       (cont (cadr exp) meta-cont))
      
      (((tagged? 'begin) exp)
       (if (null? (cddr exp))
           (evl (cadr exp) env cont meta-cont)
           (evl (cadr exp) env 
                (lambda (v mc) 
                  (evl (cons 'begin (cddr exp)) env cont mc))
                meta-cont)))
      
      (((tagged? 'let) exp)
       (let ((params (map car (cadr exp)))
             (args (map cadr (cadr exp)))
             (body (cons 'begin (cddr exp))))
         (evl (cons (list 'lambda params body) args) env cont meta-cont)))
      
      (((tagged? 'define) exp)
       (let ((old-frame (car env))
             (b (cons (cadr exp) 'undefined)))
         (let ((new-frame (cons b old-frame)))
           (set-car! env new-frame)
           (evl (caddr exp) env 
                (lambda (r mc)
                  (set-cdr! b r)
                  (cont 'undefined mc))
                meta-cont))))
      
      (((tagged? 'set!) exp)
       (evl (caddr exp) env
            (lambda (val mc)
              (let ((binding (assq (cadr exp) (car env))))
                (if binding
                    (begin
                      (set-cdr! binding val)
                      (cont 'ok mc))
                    (error 'set! "unbound variable" (cadr exp)))))
            meta-cont))
      
      (((tagged? 'if) exp)
       (evl (cadr exp) env
            (lambda (v mc)
              (if v
                  (evl (caddr exp) env cont mc)
                  (evl (cadddr exp) env cont mc)))
            meta-cont))
      
      (((tagged? 'and) exp)
       ;; assumes exactly two arguments
       (evl (list 'if (cadr exp) (caddr exp) #f) env cont meta-cont))
      
      (((tagged? 'or) exp)
       ;; assumes we only care about boolean results
       (if (null? (cdr exp))
           (cont #f meta-cont)
           (evl (list 'if (cadr exp) #t (cons 'or (cddr exp))) env cont meta-cont)))
      
      (((tagged? 'cond) exp)
       (if (null? (cdr exp))
           (cont 'undefined meta-cont)
           (let ((clause (cadr exp))
                 (rest (cddr exp)))
             (if (eq? 'else (car clause))
                 (evl (cadr clause) env cont meta-cont)
                 (evl (car clause) env
                      (lambda (v mc)
                        (if v
                            (evl (cadr clause) env cont mc)
                            (evl (cons 'cond rest) env cont mc)))
                      meta-cont)))))

      (((tagged? 'lambda) exp)
       (cont (list 'closure env (cadr exp)
                   (if (null? (cddr exp)) 
                       (cadr exp) 
                       (cons 'begin (cddr exp))))
             meta-cont))
      
      (((tagged? 'delta) exp)
       (cont (list 'delta-reifier env (cadr exp) (caddr exp))
             meta-cont))
      
      (((tagged? 'meaning) exp)
       (evl (cadr exp) env
            (lambda (e mc)
              (evl (caddr exp) env
                   (lambda (r mc)
                     (evl (cadddr exp) env
                          (lambda (k mc)
                            (evl e (cadr r) (cadr k) 
                                 (cons (cons env cont) mc)))
                          mc))
                   mc))
            meta-cont))
      
      (((tagged? 'load) exp)
       (evl (cadr exp) env
            (lambda (filename mc)
              (file-load env filename cont mc))
            meta-cont))
      
      (else
       (evl (car exp) env
            (lambda (p mc)
              (if ((tagged? 'delta-reifier) p)
                  (app p (cdr exp) env cont mc)
                  (evlis (cdr exp) env
                         (lambda (args mc)
                           (app p args env cont mc))
                         mc)))
            meta-cont)))))

(define evlis
  (lambda (exps env cont meta-cont)
    (if (null? exps)
        (cont '() meta-cont)
        (evl (car exps) env
             (lambda (v mc)
               (evlis (cdr exps) env
                      (lambda (vs mc)
                        (cont (cons v vs) mc))
                      mc))
             meta-cont))))

(define app
  (lambda (p args env cont meta-cont)
    (cond
      (((tagged? 'closure) p)
       (let ((clo-env (cadr p))
             (params (caddr p))
             (body (cadddr p)))
         (evl body (env-extend clo-env params args) cont meta-cont)))
      
      (((tagged? 'delta-reifier) p)
       (let ((forced-mc (meta-cont-force meta-cont))
             (reifier-env (cadr p))
             (params (caddr p))
             (body (cadddr p)))
         (let ((upper-env (car (car forced-mc)))
               (upper-cont (cdr (car forced-mc)))
               (upper-meta-cont (cdr forced-mc))
               (k-proc (list 'continuation (lambda (v mc) (cont v meta-cont)))))
           (evl body 
                (env-extend upper-env params 
                           (list args 
                                 (list 'environment env)
                                 k-proc))
                upper-cont
                upper-meta-cont))))
      
      (((tagged? 'environment) p)
       (let ((e (cadr p)))
         (let ((n (length args)))
           (cond
           ((= n 0) (cont e meta-cont))
           ((= n 1) (cont (env-lookup e (car args)) meta-cont))
           (else (error 'app "environment expects 0 or 1 args"))))))
      
      (((tagged? 'continuation) p)
       (let ((k (cadr p)))
         (if (= (length args) 1)
             (k (car args) meta-cont)
             (error 'app "continuation expects 1 arg"))))
      
      ((procedure? p)
       (cont (apply p args) meta-cont))

      ;; we hard code higher-order primitives
      ((eq? p 'map-primitive)
       (map-with-context (car args) (cadr args) env cont meta-cont))
      ((eq? p 'with-exception-handler-primitive)
       (with-exception-handler-with-context (car args) (cadr args) env cont meta-cont))
      ((eq? p 'call-with-input-file-primitive)
       (call-with-input-file-with-context (car args) (cadr args) env cont meta-cont))

      (else
       (error 'app (format "expected procedure, not ~a" p))))))

(define map-with-context
  (lambda (f xs env cont meta-cont)
    (define map-helper
      (lambda (xs acc)
        (if (null? xs)
            (cont (reverse acc) meta-cont)
            (app f (list (car xs)) env
                 (lambda (v mc)
                   (map-helper (cdr xs) (cons v acc)))
                 meta-cont))))
    (map-helper xs '())))

(define with-exception-handler-with-context
  (lambda (handler thunk env cont meta-cont)
    (with-exception-handler
      (lambda (exn)
        (app handler (list exn) env cont meta-cont))
      (lambda ()
        (app thunk '() env cont meta-cont)))))

(define call-with-input-file-with-context
  (lambda (filename proc env cont meta-cont)
    (call-with-input-file 
      filename
      (lambda (port)
        (app proc (list port) env cont meta-cont)))))

(define file-load-iter
  (lambda (env port last-value cont meta-cont)
    (let ((exp (read port)))
      (if (eof-object? exp)
          (begin
            (newline)
            (cont last-value meta-cont))
          (begin
            (display ".")
            (evl exp env 
                 (lambda (v mc) 
                   (file-load-iter env port v cont mc))
                 meta-cont))))))

(define file-load
  (lambda (env filename cont meta-cont)
    (call-with-input-file filename
      (lambda (port) 
        (file-load-iter env port 'undefined cont meta-cont)))))

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
     (cons 'reify-env (lambda () (list 'environment (make-global-env))))
     (cons 'reify-cont (lambda () (list 'continuation 
                                        (lambda (v mc) 
                                          (display "Result: ")
                                          (display v)
                                          (newline)
                                          v)))))))

(define make-global-env
  (lambda ()
    (cons (make-global-frame) '())))

(print-graph #t)

(define repl-loop
  (lambda (evl env meta-cont level iter)
    (newline) 
    (display level) (display "-") (display iter) (display "> ")
    (let ((exp (read)))
      (cond
        ((eof-object? exp)
         (display ";<eof>\n")
         (let ((forced-mc (meta-cont-force meta-cont)))
           (let ((upper-env (car (car forced-mc)))
                 (upper-cont (cdr (car forced-mc)))
                 (upper-meta-cont (cdr forced-mc)))
             (upper-cont 'exit-level upper-meta-cont))))
        (else
         (with-exception-handler
          (lambda (c)
            (display ";Error: ") (display-condition c) (newline)
            (repl-loop evl env meta-cont level (+ iter 1)))
          (lambda ()
            (let ((start (cpu-time)))
              ((evl exp env
                    (lambda (v mc)
                      (let ((elapsed (- (cpu-time) start)))
                        (display ";==> ") (write v)
                        (newline)
                        (display ";(") (display elapsed) (display " cpu-time)")
                        (newline)
                        (repl-loop evl env mc level (+ iter 1))))
                    meta-cont)
               )))))))))

(define repl
  (lambda (level)
    (repl-loop evl (make-global-env) (get-meta-cont 1) level 0)))
