(load "lc-tests.scm")

(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define empty-env (lambda (y) (error 'env (format "unbound variable: ~s" y))))

(define lc-cps
  (lambda (exp env k)
    (cond
     ((symbol? exp) (k (env exp)))
     ((boolean? exp) (k exp))
     ((number? exp) (k exp))
     (((tagged? 'sub1) exp)
      (lc-cps (cadr exp) env (lambda (v) (k (sub1 v)))))
     (((tagged? 'zero?) exp)
      (lc-cps (cadr exp) env (lambda (v) (k (zero? v)))))
     (((tagged? '*) exp)
      (lc-cps (cadr exp) env (lambda (v1)
                               (lc-cps (caddr exp) env (lambda (v2)
                                                         (k (* v1 v2)))))))
     (((tagged? 'if) exp)
      (lc-cps (cadr exp) env (lambda (vc)
                           (if vc
                               (lc-cps (caddr exp) env k)
                               (lc-cps (cadddr exp) env k)))))
     (((tagged? 'lambda) exp)
      (let ((x (car (cadr exp)))
            (body (caddr exp)))
        (k (lambda (a k)
             (lc-cps body
                     (lambda (y) (if (eq? x y) a (env y)))
                     k)))))
     (else
      (lc-cps (car exp) env (lambda (vrator)
                              (lc-cps (cadr exp) env (lambda (vrand)
                                                       (vrator vrand k)))))))))

(define lc
  (lambda (exp env)
    (lc-cps exp env (lambda (v) v))))


(lc-tests lc empty-env)
