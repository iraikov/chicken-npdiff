
;;
;; Compute the longest common subsequence of two sequences 
;;
;; Copyright 2007-2018 Ivan Raikov.
;;
;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; A full copy of the GPL license can be found at
;; <http://www.gnu.org/licenses/>.

(module npdiff

 (export diffop diffop? Insert Remove Change
	 npdiff make-hunks)
		   
 (import scheme (chicken base) srfi-1 srfi-4 datatype
         yasos yasos-collections)


 

(include "box.scm")
(include "stack.scm")

(define (psplit2 lst) (values (car lst) (cdr lst)))

(define (intpair? x)
  (and (pair? x) (integer? (car x)) (integer? (cdr x))))


; Datatype: diffop
;
; A representation of the three diff operations; insert, remove, change. 
;
; TARGET is the line or range of lines that is being operated on
;
; SOURCE is the range of lines that is used as input of the insert and
; change commands.  
;
; DATA, DATAIN, DATAOUT is a sequence of the
; elements (e.g. lines) that are being inserted or replaced.
;
; CONTEXT, CONTEXTIN, CONTEXTOUT is optional context; these are pairs
; in which the car is a list of elements preceding the operation, and
; the cdr is a list of elements following the operation.
;
(define-datatype diffop diffop?
  (Insert   (target integer?) (source intpair?)
	    (seq collection?) (context (lambda (x) (or (not x) (collection? x)))) )
  (Remove   (target intpair?)
	    (seq collection?) (context (lambda (x) (or (not x) (collection? x)))) )
  (Change   (target intpair?)
	    (source intpair?)
	    (seqin collection?)
	    (seqout collection?)
	    (contextin (lambda (x) (or (not x) (collection? x))))
	    (contextout (lambda (x) (or (not x) (collection? x))))))


(define-record-printer (diffop x out)
  (cases diffop x 
	 (Insert (target source seq context)
		 (display "#(Insert" out)
		 (display (conc " target=" target) out)
		 (display (conc " source=" source) out)
		 (display (conc " seq=" seq) out)
		 (display (conc " context=" context) out)
		 (display ")" out))
	 
	 (Remove (target seq context)
		 (display "#(Remove " out)
		 (display (conc " target=" target) out)
		 (display (conc " seq=" seq) out)
		 (display (conc " context=" context) out)
		 (display ")" out))
	 
	 (Change (target source seqin seqout contextin contextout)
		 (display "#(Change" out)
		 (display (conc " target=" target) out)
		 (display (conc " source=" source) out)
		 (display (conc " seqin=" seqin) out)
		 (display (conc " seqout=" seqout) out)
		 (display (conc " contextin=" contextin) out)
		 (display (conc " contextout=" contextout) out)
		 (display ")" out))))


;;
;;
;;  S. Wu, U. Manber, and E. Myers. An O(NP) sequence comparison
;;  algorithm. In Information Processing Letters, volume 35, pages
;;  317--323, September 1990.
;;
;;
(define (npdiff A B . rest)
   (let-optionals  rest ((context-len 0))
    (define css (make-stack))

    (let ((M (size A))
	  (N (size B)))

      (let-values (((A B M N swap) 
		    (if (> M N) (values B A N M #t)
			(values A B M N #f))))

       ;; The algorithm outlined in the paper calls for the creation
       ;; of an array that contains the furthest paths, and that is
       ;; defined as [-(M+1),(N+1)].

       ;; Since the vector library in Scheme does not support negative
       ;; array indices, we are going to have to bump everything by
       ;; offset M+1 whenever accessing array FP

       (define (compare delta offset fp p) 
	 
	 (define (update k)
	   (s32vector-set! fp (+ k offset)
			   (snake k (max (+ 1 (s32vector-ref fp (+ offset (- k 1))))
					 (s32vector-ref fp (+ offset (+ 1 k)))))))
      
	 (define (lowerloop k)
	   (if (<= k (- delta 1))
	       (begin
		 (update k)
		 (lowerloop (+ 1 k)))))
	 
	 (define (upperloop k)
	   (if (>= k (+ 1 delta))
	       (begin
		 (update k)
		 (upperloop (- k 1)))))
	 
	 (let ((p (+ p 1)))
	   (lowerloop (* -1 p))
	   (upperloop (+ delta p))
	   (update delta)
	   (if (not (= N (s32vector-ref fp (+ offset delta))))
	       (compare delta offset fp p))))
       
		  
       (define (snake k y)
	 (let ((a (- y k))
	       (b y))
	   (let-values ((( x y ) 
			 (let loop ((x  a)  (y  b))
			   (if (and (< x M) (< y N)
				    (equal? (elt-ref A x) (elt-ref B y)))
			       (loop (+ 1 x) (+ y 1))
			       (values x y)))))
		       (if (or (not (= a x)) (not (= b y)))
			   (let-values (((lasta lastb)
					 (if (stack-empty? css) (values -1 -1)
					     (psplit2 (car (stack-rest css))))))
			       (if (and (< lasta a) (< lastb b))
				   ;; we have found a common substring; push the end
				   ;; and start pairs onto the common substring stack
				   (if swap
				       (begin
					 (stack-push! css (cons b a))
					 (stack-push! css (cons y x)))
				       (begin
					 (stack-push! css (cons a b))
					 (stack-push! css (cons x y)))))))
		       y)))


       (let ((offset (+ 1 M))
	     (fp     (make-s32vector (+ 3 (+ M N)) -1))
	     (delta  (- N M))
	     (p       -1))
	 (compare delta offset fp p)
	 (if swap 
	     (values (make-hunks B A css context-len) B A)
	     (values (make-hunks A B css context-len) A B))))))))




;;  Pop matching pairs from the given stack, and fill in the gaps
;;  between them with insert/change/remove hunks.
;;
;;  This function expects the following stack layout:
;;
;; 	endpair n
;; 	startpair n
;; 	endpair n-1
;;      startpair n-1
;; 	.
;; 	.
;; 	.
;; 	endpair 1
;; 	startpair 1
;;			 
;;  i.e. the one constructed by function `npdiff' above. endpair
;;  marks the end of a common substring. startpair marks the beginning
;;  of a common substring. Each pair has the form (x,y) where x is a
;;  line number in text A, and y is a line number in text B.
;;
;;  If substring n (i.e. the one at the top of the stack) does not
;;  reach the last line of text A (its endpair does NOT have the last
;;  line number in A as x coordinate) that means we have some extra
;;  lines at the end of text A that need to be removed, so we make a
;;  remove hunk for them. If instead the y component does not reach
;;  the end of B, we make an insert hunk.
;;
;;  If substring 1 (i.e. the one at the bottom of the stack) does not
;;  start from the first line of text A (its endpair does NOT have 0
;;  as y coordinate) that means we have some extra lines at the
;;  beginning of text B that need to be inserted, so we make an insert
;;  hunk for them. If instead the x component is non-zero, we make a
;;  remove hunk.
;;
;;  For all other cases, we make change hunks that fill in the gaps
;;  between any two common substrings.  
(define (make-hunks A B css . rest)
  
    (let-optionals  rest ((context-len 0))
     (let ((M (size A))
	   (N (size B))
	   (context? (> context-len 0)))
       
       (define (make-context seq len start end)
	 (if (or (> start len) (< end start)) (list)
	     (let ((start (if (< start 0) 0 start))
		   (end   (if (< len end) len end)))
	       (slice seq start end))))
       
       (define (loop css hunks)
	 (if (stack-empty? css) hunks
	    ;; make a change hunk and recurse
	    (let-values (((endpair startpair)  (stack-ppeek css)))
	      (let ((k (stack-depth css)))
		(let-values (((x y)  (psplit2 startpair))
			     ((w z)  (psplit2 endpair)))
		    ;; are these the the last two elements of the stack?
		    (if (= 1 k)
			(cond ((and (= 0 x) (= 0 y))   hunks)

			      ((= 0 x) (cons (Insert x (cons 0 y) (slice B 0 y) 
					       (and context? (cons (list) (make-context B N y (+ y context-len)))))
					       hunks))

			      ((= 0 y) (cons (Remove (cons 0 x) (slice A 0 x)
						       (cons (list) (make-context A M x (+ x context-len))))
					       hunks))

			      (else (cons (Change (cons 0 x) (cons 0 y)
						  (is-slice B 0 y) (slice A 0 x) 
						  (and context? (cons (list) (make-context B N y (+ y context-len))))
						  (and context? (cons (list) (make-context A M x (+ x context-len)))))
					  hunks)))
			(begin
			  (stack-pop! css)
			  (stack-pop! css)
			  (let-values (((w z) (values x y))
				       ((x y) (psplit2 (stack-peek css))))
                            (let ((newhunk  (cond ((= y z)  
						   (Remove (cons x w) (slice A x w)
							   (and context? 
								(cons (make-context A M (- x context-len) x)
								      (make-context A M x (+ w context-len))))))
						  
						  ((= x w)  
						   (Insert x (cons y z) (is-slice B y z)
							   (and context? 
								(cons (make-context B N (- y context-len) y)
								      (make-context B N z (+ z context-len))))))

						  (else (Change (cons x w) (cons y z)
								(is-slice B y z ) (slice A x w)
								(and context? 
								     (cons (make-context B N (- y context-len) y)
									   (make-context B N z (+ z context-len))))
								(and context?
								     (cons (make-context A M (- x context-len) x)
									   (make-context A M w (+ w context-len)))))))))
;;			      (match hunks
;;				     ((h . rest)  (loop css (merge newhunk h rest)))
			      (loop css (if newhunk (cons newhunk hunks) hunks)))))))))))

      (if (stack-empty? css)

	  (cond ((and (zero? M) (zero? N)) ;; both sequences are empty
		 (list))
		
		((zero? M) ;; sequence A is empty
		 (list (Insert 0 (cons 0 N) (slice B 0 N) (and context? `(())))))

		((zero? N) ;; sequence B is empty
		 (list (Remove (cons 0 M) (slice A 0 M)   (and context? `(())))))

		;; the two sequences are completely different
		(else
		 (list (Change (cons 1 M) (cons 1 N)
			       (slice B 0 N)
			       (slice A 0 M)
			       (and context? (cons (make-context B N 0 N) (list)))
			       (and context? (cons (make-context A M 0 M) (list))))))
		)

	  (let-values (((endpair startpair)  (stack-ppeek css)))
	     (let ((k (stack-depth css)))
		(let-values (((x y)  (psplit2 startpair))
			     ((w z)  (psplit2 endpair)))

                  (cond ((and (= w M) (= z N))

			 (loop css (list)))

			((= z N)
			 (loop css (list (Remove (cons w M) (slice A w M)
						 (and context? (cons (make-context A M w (+ w context-len))
								     (list)))))))

			((= w M)
			 (loop css (list (Insert w (cons z N) (slice B z N)
						 (and context? (cons (make-context B N (- z context-len) z)
								     (list)))))))

			(else (loop css (list (Change (cons w M) (cons z N)
						      (slice B z N )
						      (slice A w M)
						      (and context? (cons (make-context B N (- z context-len) z)
									  (list)))
						      (and context? (cons (make-context A M (- w context-len) w)
									  (list)))
						      )))
			      ))
		  ))
	     ))))))



)
