(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define empty-env (lambda (y) (error 'env "unbound variable")))

(define (make-global-env) empty-env)

(define make-meta-cont-level
  (lambda (level)
    (let ((upper-env (make-global-env)))
      (cons upper-env
            (lambda (val mc)
              (display (format "Returned to level ~a with: " level))
              (display val)
              (newline)
              '(repl-loop evl upper-env mc level 0))))))

(define get-meta-cont
  (lambda (level)
    (cons (make-meta-cont-level level)
          (lambda () (get-meta-cont (+ level 1))))))

(define meta-cont-force
  (lambda (mc)
    (if (procedure? (cdr mc))
        (cons (car mc) ((cdr mc)))
        mc)))

(define lc-tower
  (lambda (exp env k meta-k)
    (cond
     ((symbol? exp) (k (env exp) meta-k))
     ((boolean? exp) (k exp meta-k))
     ((number? exp) (k exp meta-k))
     (((tagged? 'sub1) exp)
      (lc-tower (cadr exp) env (lambda (v mc) (k (sub1 v) mc)) meta-k))
     (((tagged? 'zero?) exp)
      (lc-tower (cadr exp) env (lambda (v mc) (k (zero? v) mc)) meta-k))
     (((tagged? '*) exp)
      (lc-tower (cadr exp) env (lambda (v1 mc)
                                 (lc-tower (caddr exp) env (lambda (v2 mc)
                                                             (k (* v1 v2) mc))
                                           mc))
              meta-k))
     (((tagged? 'if) exp)
      (lc-tower (cadr exp) env (lambda (vc mc)
                                 (if vc
                                     (lc-tower (caddr exp) env k mc)
                                     (lc-tower (cadddr exp) env k mc)))
                meta-k))
     (((tagged? 'lambda) exp)
      (let ((x (car (cadr exp)))
            (body (caddr exp)))
        (k (lambda (a k mc)
             (lc-tower body
                       (lambda (y) (if (eq? x y) a (env y)))
                       k mc))
           meta-k)))
     (else
      (lc-tower (car exp) env (lambda (vrator mc)
                                (lc-tower (cadr exp) env (lambda (vrand mc)
                                                           (vrator vrand k mc))
                                          mc))
                meta-k)))))

(define lc
  (lambda (exp env)
    (lc-tower exp env (lambda (v mc) v) (get-meta-cont 0))))

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
