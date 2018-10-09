;; Scheme

;; lambda-calculus
(lambda (x) x) ;; #<procedure>
((lambda (x) x) (lambda (x) x))
((lambda (x) x) 1) ;; 1

;; LISP
;; list processing
(cons 1 '()) ;; (1)
(list 1) ;; (1)
(cons 1 2) ;; (1 . 2)
(car (cons 1 2)) ;; first
(cdr (cons 1 2)) ;; rest
(cdr (list 1 2))
(cdr (cons 1 (cons 2 '())))

;; program as data
(if (= 1 2) 'hello 'there)
(if (eq? 'hello 'hello) 'yes 'no)

;(car (cons A B)) == A
;(cdr (cons A B)) == B

(define my-cons
  (lambda (a b)
    (lambda (msg)
      (if (eq? msg 'car) a b))))

(define my-car
  (lambda (p)
    (p 'car)))

(define my-cdr
  (lambda (p)
    (p 'cdr)))

(my-car (my-cons 1 2))
(my-cdr (my-cons 1 2))

;; data as program

(list 'a 'b 'c)
'(a b c)
(car '(if (= 1 2) 3 4))
(cadr '(if (= 1 2) 3 4))
(caddr '(if (= 1 2) 3 4))
(cadddr '(if (= 1 2) 3 4))

;; primitives
;; mean of combination
;; mean of abstraction
(define x 3)
x
(define f (lambda (x y) (+ 1 (* x y))))
(f 3 4)

(define my-if (lambda (a b c)
                (if a b c)))

;;divides by zero: (my-if (= 1 1) 1 (/ 1 0))

'(/ 1 0)
;;==
(quote (/ 1 0))

(if 1 2 3)

((lambda (x y) y) 1 2)

(((lambda (x) (lambda (y) y)) 1) 2)

(define frame1 '((x . 1) (y . 2)))
(define frame2 '((z . 3) (x . 2)))
(assq 'x frame1)
(assq 'x frame2)
(define env1
  (list frame1 frame2 '()))
;(env-lookup env1 'x) ;; 1
;(env-lookup env1 'z) ;; 3
