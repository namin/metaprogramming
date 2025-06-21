(load "tower.scm")

(define make-meta-cont-level-with
  (lambda (level)
    (let ((m (make-meta-cont-level level)))
      ;; add a frame with the level as a variable
      (cons (cons (list (cons 'level level)) (car m)) (cdr m)))))

;; overwrite
(define get-meta-cont
  (let ((m0 (make-meta-cont-level-with 0)) 
        (m1 (make-meta-cont-level-with 1)))
    (let ((mc (cons m0 (cons m1 #f))))
      (set-cdr! (cdr mc) mc) ;; cycle
      (lambda (level)
        (if (= (modulo level 2) 0)
            mc
            (cdr mc))))))
