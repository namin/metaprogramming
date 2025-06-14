(load "lc-tests.scm")

(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define empty-env (lambda (y) (error 'env "unbound variable")))

(define (make-global-env) empty-env)

(define (env-extend env params args)
  (if (null? params)
      env
      (let ((x (car params))
            (a (car args)))
        (env-extend (lambda (y) (if (eq? x y) a (env y))) (cdr params) (cdr args)))))

(define make-meta-cont-level
  (lambda (level)
    (let ((upper-env (make-global-env)))
      (cons upper-env
            (lambda (val mc)
              (display (format "Returned to level ~a with: " level))
              (display val)
              (newline)
              val)))))

(define get-meta-cont
  (lambda (level)
    (cons (make-meta-cont-level level)
          (lambda () (get-meta-cont (+ level 1))))))

(define meta-cont-force
  (lambda (mc)
    (if (procedure? (cdr mc))
        (cons (car mc) ((cdr mc)))
        mc)))

(define lc
  (lambda (exp env)
    (cond
     ((symbol? exp) (env exp))
     ((boolean? exp) exp)
     ((number? exp) exp)
     (((tagged? 'sub1) exp)
      (sub1 (lc (cadr exp) env)))
     (((tagged? 'zero?) exp)
      (zero? (lc (cadr exp) env)))
     (((tagged? '*) exp)
      (* (lc (cadr exp) env) (lc (caddr exp) env)))
     (((tagged? 'if) exp)
      (if (lc (cadr exp) env)
          (lc (caddr exp) env)
          (lc (cadddr exp) env)))
     (((tagged? 'lambda) exp)
      (let ((x (car (cadr exp)))
            (body (caddr exp)))
        (lambda (a)
          (lc body
              (lambda (y) (if (eq? x y) a (env y)))))))
     (else
      ((lc (car exp) env) (lc (cadr exp) env))))))

(lc-tests lc empty-env)

(define (lc-reflective-tests lc empty-env)
  (eg (lc '((mu (e r) (meaning 1 r))) empty-env) 1)
  (eg (lc '((mu (e r) (meaning (car e) r)) 1) empty-env) 1)
  (eg (lc '((mu (e r) (meaning (car e) r)) (sub1 2)) empty-env) 1)
  (eg (lc '((mu (e1 r1) ((delta (e2 r2) (meaning 1 r2))))) empty-env) 1)
)

;(lc-reflective-tests lc empty-env)

