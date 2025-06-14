(load "lc-tests.scm")

(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define empty-env (lambda (y) (error 'env "unbound variable")))

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
