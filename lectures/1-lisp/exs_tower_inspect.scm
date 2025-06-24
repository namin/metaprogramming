(define foo (lambda (f) (lambda (x) (lambda () (f (+ x 1))))))
(define thunk ((foo 2) 3))
(thunk)
(old-cont 'ok)

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

(inspect thunk)

(thunk)
