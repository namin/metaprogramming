(load "tower.scm")
(repl 0)
;; 0-0>
(define foo (lambda (f) (lambda (x) (lambda () (f (+ x 1))))))
;; ==> undefined
;; 0-1>
(define thunk ((foo 2) 3))
;; ==> undefined
;; 0-2>
(thunk)
;; Error: Exception in app: expected procedure, not 2
;; Returned to level 1 with: undefined
;; 1-0>
(old-cont 'ok)
;; Continuing with ok
;; 0-3>
(define inspect
  (lambda (c)
    ((delta (e r k)
       (let ((env (cadr (r 'c))))
         (define loop
           (lambda ()
             (display "inspect> ")
             (let ((exp (read)))
               (cond
                 ((and (pair? exp) (eq? (car exp) 'exit))
                  (meaning (cadr exp) env k))
                 (else
                  (meaning exp env (lambda (v) (write v) (newline) (loop))))))))
         (loop))))))
;; ==> undefined
;; 0-4>
(inspect thunk)
;; inspect>
f
;; 2
;; inspect>
(set! f (lambda (x) (* 2 x)))
;; undefined
;; inspect>
(exit 0)
;; ==> 0
;; 0-5>
(thunk)
;; ==> 8
