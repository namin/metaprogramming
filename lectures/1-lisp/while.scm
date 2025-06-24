(define-syntax while
  (syntax-rules ()
    ((_ c b r)
     (let loop ()
       (if c
           (begin
             b
             (loop))
           r)))))
