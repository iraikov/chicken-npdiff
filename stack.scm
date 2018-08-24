
;; Stack routines.  Based on dfa2.sc in the benchmarks code supplied
;; with Stalin 0.11

(define (make-stack)
  (box '()))

(define (stack-empty? s)
  (null? (unbox s)))

(define (stack-push! s obj)
  (set-box! s (cons obj (unbox s)))
  s)

(define (stack-pop! s)
  (let ((l (unbox s)))
    (set-box! s (cdr l))
    (car l)))

(define (stack-depth s)
  (let ((l (unbox s)))
    (- (length l) 1)))

(define (stack-peek s)
  (let ((l (unbox s)))
    (car l)))

(define (stack-ppeek s) 
  (let ((l (unbox s)))
    (values (car l)  (car (cdr l)))))

(define (stack-rest s)
  (let ((l (unbox s)))
    (cdr l)))
