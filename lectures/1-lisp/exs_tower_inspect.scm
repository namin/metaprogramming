(define f ((lambda (x) (lambda (y) (+ x y))) 3))
(f 7)
((delta (e r k) (begin (set-cdr! (car (car (cadr (r 'f)))) 5) (k 0))))

(define foo (lambda (f) (lambda (x) (lambda () (f (+ x 1))))))
(define thunk ((foo 2) 3))
(thunk)
(old-cont 'ok)

((delta (e r k)
  (begin
    (load "tower.scm")
    (let ((b (find-binding (cadr (r 'thunk)) 'f)))
      (set-cdr! b (lambda (x) (* 2 x)))
      (k 0)))))


