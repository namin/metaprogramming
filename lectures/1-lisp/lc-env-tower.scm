(load "lc-tests.scm")

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
      upper-env)))

(define get-meta-cont
  (lambda (level)
    (cons (make-meta-cont-level level)
          (lambda () (get-meta-cont (+ level 1))))))

(define meta-cont-force
  (lambda (mc)
    (if (procedure? (cdr mc))
        (cons (car mc) ((cdr mc)))
        mc)))

(define lc-meta
  (lambda (exp env meta-k)
    (cond
     ((symbol? exp) (env exp))
     ((boolean? exp) exp)
     ((number? exp) exp)
     (((tagged? 'sub1) exp)
      (sub1 (lc-meta (cadr exp) env meta-k)))
     (((tagged? 'zero?) exp)
      (zero? (lc-meta (cadr exp) env meta-k)))
     (((tagged? 'car) exp)
      (car (lc-meta (cadr exp) env meta-k)))
     (((tagged? '*) exp)
      (* (lc-meta (cadr exp) env meta-k) (lc-meta (caddr exp) env meta-k)))
     (((tagged? 'if) exp)
      (if (lc-meta (cadr exp) env meta-k)
          (lc-meta (caddr exp) env meta-k)
          (lc-meta (cadddr exp) env meta-k)))
     (((tagged? 'lambda) exp)
      (let ((x (car (cadr exp)))
            (body (caddr exp)))
        (lambda (a)
          (lc-meta body
                   (lambda (y) (if (eq? x y) a (env y)))
                   meta-k))))

     ;; reflective procedures

      (((tagged? 'mu) exp)
       (list 'mu-reifier env (cadr exp) (caddr exp)))
      (((tagged? 'meaning) exp)
       (let* ((e (lc-meta (cadr exp) env meta-k))
              (r (lc-meta (caddr exp) env meta-k)))
         (lc-meta e r (cons env meta-k))))

     (else
      (let ((p (lc-meta (car exp) env meta-k)))
        (if ((tagged? 'mu-reifier) p)
            (let ((forced-mc (meta-cont-force meta-k))
                  (reifier-env (cadr p))
                  (params (caddr p))
                  (body (cadddr p)))
              (let ((upper-env (car forced-mc))
                    (upper-meta-cont (cdr forced-mc)))
                (lc-meta body
                         (env-extend upper-env params
                                     (list (cdr exp)
                                           env))
                          upper-meta-cont)))
            (p (lc-meta (cadr exp) env meta-k))))))))

(define lc
  (lambda (exp env)
    (lc-meta exp env (get-meta-cont 0))))

(lc-tests lc empty-env)

(define (lc-reflective-tests lc empty-env)
  (eg (lc '((mu (e r) (meaning 1 r))) empty-env) 1)
  (eg (lc '((mu (e r) (meaning (car e) r)) 1) empty-env) 1)
  (eg (lc '((mu (e r) (meaning (car e) r)) (sub1 2)) empty-env) 1)
  (eg (lc '((mu (e1 r1) ((mu (e2 r2) (meaning 1 r2))))) empty-env) 1)
)

(lc-reflective-tests lc empty-env)

