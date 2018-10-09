((lambda (f1)
   (f1 f1 6))
 (lambda (f n)
   (if (< n 2) 1
       (* n (f f (- n 1))))))

(define fact
  (lambda (n)
    (if (< n 2) 1
        (* n (fact (- n 1))))))
