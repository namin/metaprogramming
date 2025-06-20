;; Example demonstrating causally connected reflective tower
;; with meta-level memoization that changes object-level computation

(define fib-memo-cache '())

(define fib
  (lambda (n)
    (cond
      ((= n 0) 0)
      ((= n 1) 1)
      (else (+ (fib (- n 1)) (fib (- n 2)))))))

(define memo-reifier
(delta (e r k)
       (let ((exp (car e))
             (key-call (r 'memo-key-call))
             (key-cache (r 'memo-key-cache)))
         (if (and (pair? exp) (eq? (car exp) key-call))
             ;; Intercept calls to functions we want to memoize
             (begin
               (display "Intercept call\n")
               (let ((args (cdr exp)))
                 (let ((cache (r key-cache)))
                   (let ((cached-entry (assoc args cache)))
                     (if cached-entry
                         ;; CAUSAL EFFECT: Return cached value, skip computation
                         (begin
                           (display "Meta-level: Cache hit")
                           (display args)
                           (display " -> ")
                           (display (cdr cached-entry))
                           (newline)
                           (k (cdr cached-entry)))
                         ;; Not cached: compute, store result, then return it
                         (begin
                           (display "Not cached, computing...\n")
                           (meaning exp r
                                    (lambda (result)
                                      ;; Cache the result at meta-level
                                      (display "Caching result\n")
                                      (r key-cache (cons (cons args result) cache))
                                      (display "Meta-level: Cached")
                                      (display args)
                                      (display " -> ")
                                      (display result)
                                      (newline)
                                      (k result)))))))))
             ;; For non-memoized expressions, evaluate normally
             (meaning exp r k)))))

(define memo-key-call 'fib)
(define memo-key-cache 'fib-memo-cache)
(memo-reifier (fib 6))
(memo-reifier (fib 6))
fib-memo-cache
