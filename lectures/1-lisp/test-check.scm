(define-syntax eg
  (syntax-rules ()
    ((_ tested-expression expected-result)
     (begin
       (printf "Testing ~a is ~a\n"
         (quote tested-expression)
         (quote expected-result))
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'eg
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~a\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define-syntax test-disable
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Disable testing ~s\n" title)
       #t))))
