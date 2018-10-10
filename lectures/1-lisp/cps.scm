;; Continuation-Passing Style

;; Factorial Direct Style
(define factorial
    (lambda (n)
      (if (< n 2) 1
          (* n (factorial (- n 1))))))

;; Factorial CPS
(define factorial-cps
    (lambda (n k)
      (if (< n 2) (k 1)
          (factorial-cps (- n 1) (lambda (v)
                                   (k (* n v)))))))
(define factorial
  (lambda (n)
    (factorial-cps n (lambda (v) v))))

;; Factorial CPS Trampoline

(define factorial-cps
  (lambda (n k)
    (lambda ()
      (if (< n 2) (k 1)
          (factorial-cps (- n 1) (lambda (v)
                                   (k (* n v))))))))

(define loop
  (lambda (r)
    (while (procedure? r)
           (set! r (r))
           r)))

(define factorial
  (lambda (n)
    (loop (factorial-cps n (lambda (v) v)))))

;; Evaluator

(define lc
  (lambda (exp env)
    (if (symbol? exp)
        (env exp)
        (if (pair? exp)
            (if (eq? (car exp) 'sub1)
                (- (lc (car (cdr exp)) env) 1)
                (if (eq? (car exp) 'zero?)
                    (= (lc (car (cdr exp)) env) 0)
                    (if (eq? (car exp) '*)
                        (* (lc (car (cdr exp)) env)
                           (lc (car (cdr (cdr exp))) env))
                        (if (eq? (car exp) 'if)
                            (if (lc (car (cdr exp)) env)
                                (lc (car (cdr (cdr exp))) env)
                                (lc (car (cdr (cdr (cdr exp)))) env))
                            (if (eq? (car exp) 'lambda)
                                (lambda (a)
                                  (lc (car (cdr (cdr exp)))
                                      (lambda (y) (if (eq? (car (car (cdr exp))) y) a (env y)))))
                                ((lc (car exp) env)
                                 (lc (car (cdr exp)) env)))))))
            exp))))

;; example run
(lc
 '(((lambda (fun)
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
 (lambda (y) 0))
;; => 720

;; Evaluator in CPS

(define lc-cps
  (lambda (exp env k)
    (if (symbol? exp)
        (k (env exp))
        (if (pair? exp)
            (if (eq? (car exp) 'sub1)
                (lc-cps (car (cdr exp)) env (lambda (v) (k (- v 1))))
                (if (eq? (car exp) 'zero?)
                    (lc-cps (car (cdr exp)) env (lambda (v) (k (= v 0))))
                    (if (eq? (car exp) '*)
                        (lc-cps (car (cdr exp)) env (lambda (v1)
                                                      (lc-cps (car (cdr (cdr exp))) env (lambda (v2)
                                                                                          (k (* v1 v2))))))
                        (if (eq? (car exp) 'if)
                            (lc-cps (car (cdr exp)) env (lambda (vc)
                                                          (if vc
                                                              (lc-cps (car (cdr (cdr exp))) env k)
                                                              (lc-cps (car (cdr (cdr (cdr exp)))) env k))))
                            (if (eq? (car exp) 'lambda)
                                (k (lambda (a k)
                                     (lc-cps (car (cdr (cdr exp)))
                                             (lambda (y) (if (eq? (car (car (cdr exp))) y) a (env y)))
                                             k)))
                                (lc-cps (car exp) env (lambda (vrator)
                                                        (lc-cps (car (cdr exp)) env (lambda (vrand)
                                                                                      (vrator vrand k))))))))))
            (k exp)))))

(define lc
  (lambda (exp env)
    (lc-cps exp env (lambda (v) v))))
