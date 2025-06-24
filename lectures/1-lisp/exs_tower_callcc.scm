(define call/cc
  (delta (e r k)
    (meaning (list (car e) (list 'quote k)) r k)))

(+ 1 (call/cc (lambda (k) (+ (k 3) (k 6)))))
