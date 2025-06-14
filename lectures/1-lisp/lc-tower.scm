(load "test-check.scm")

(define tagged?
  (lambda (t)
    (lambda (e)
      (and (pair? e) (eq? t (car e))))))

(define empty-env (lambda (y) (error 'env (format "unbound variable: ~s" y))))

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
     (((tagged? 'car) exp)
      (lc-tower (cadr exp) env (lambda (v mc) (k (car v) mc)) meta-k))
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

     ;; reflective procedures

      (((tagged? 'delta) exp)
       (k (list 'delta-reifier env (cadr exp) (caddr exp))
          meta-k))
      (((tagged? 'meaning) exp)
       (lc-tower (cadr exp) env
                 (lambda (e mc)
                   (lc-tower (caddr exp) env
                        (lambda (r mc)
                          (lc-tower (cadddr exp) env
                                    (lambda (k mc)
                                      (lc-tower e r k
                                                (cons (cons env k) mc)))
                                    mc))
                        mc))
                 meta-k))

     (else
      (lc-tower (car exp) env (lambda (p mc)

                                (if ((tagged? 'delta-reifier) p)
                                    (let ((forced-mc (meta-cont-force meta-k))
                                          (reifier-env (cadr p))
                                          (params (caddr p))
                                          (body (cadddr p)))
                                      (let ((upper-env (car (car forced-mc)))
                                            (upper-cont (cdr (car forced-mc)))
                                            (upper-meta-cont (cdr forced-mc))
                                            (k-proc (lambda (v mc) (k v meta-k))))
                                        (lc-tower body
                                                  (env-extend upper-env params
                                                              (list (cdr exp)
                                                                    env
                                                                    k-proc))
                                                  upper-cont
                                                  upper-meta-cont)))

                                    (lc-tower (cadr exp) env (lambda (vrand mc)
                                                               (p vrand k mc))
                                              mc)
                                    ))
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

(define (lc-reflective-tests lc empty-env)
  (define my-env (env-extend empty-env '(e r k) '(1 2 3)))
  (eg (my-env 'e) 1)
  (eg (my-env 'r) 2)
  (eg (my-env 'k) 3)

  (eg (lc '((delta (e r k) (meaning 1 r k))) empty-env) 1)
  (eg (lc '((delta (e r k) (meaning (car e) r k)) 1) empty-env) 1)
  (eg (lc '((delta (e r k) (meaning (car e) r k)) (sub1 2)) empty-env) 1)
  (eg (lc '((delta (e1 r1 k1) ((delta (e2 r2 k2) (meaning 1 r2 k2))))) empty-env) 1))

(lc-reflective-tests lc empty-env)
