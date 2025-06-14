;; translated from
;; https://github.com/namin/lambdajam/blob/master/lc-sol.scm#L51

(load "test-check.scm")

(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define empty-env (lambda (y) (error 'env "unbound variable")))

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


(define (lc-tests lc empty-env)
  (eg (lc #f empty-env) #f)
  (eg (lc '(if #f #t #f) empty-env) #f)
  (eg (lc '(((lambda (fun)
               ((lambda (F)
                  (F F))
                (lambda (F)
                  (fun (lambda (x) ((F F) x))))))
             (lambda (factorial)
                (lambda (n)
                  (if (zero? n)
                      1
                      (* n (factorial (sub1 n)))))))
            6)
          empty-env)
      720))

(lc-tests lc empty-env)
