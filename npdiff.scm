
;;
;; Compute the longest common subsequence of two sequences 
;;
;; Copyright 2007-2020 Ivan Raikov.
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

 (diffop diffop? Insert Remove Change
	 npdiff make-hunks
         diffop->sexp
         format-hunks/normal
         format-hunks/ed
         format-hunks/rcs
         format-hunks/context
         )
		   
 (import scheme (chicken base) (chicken string) srfi-1 srfi-4 datatype
         yasos yasos-collections dyn-vector)


 

(include "box.scm")
(include "stack.scm")

(define (psplit2 lst) (values (car lst) (cdr lst)))

(define (intpair? x)
  (and (pair? x) (integer? (car x)) (integer? (cdr x))))

(define (context? x)
  (and (pair? x) (collection? (car x)) (collection? (cdr x))))
         
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
; in which the car is a collection of elements preceding the operation, and
; the cdr is a collection of elements following the operation.
;
(define-datatype diffop diffop?
  (Insert   (target integer?) (source intpair?)
	    (seq collection?) (context (lambda (x) (or (not x) (context? x)))) )
  (Remove   (target intpair?)
	    (seq collection?)
            (context (lambda (x) (or (not x) (context? x)))))
  (Change   (target intpair?)
	    (source intpair?)
	    (seqin collection?)
	    (seqout collection?)
	    (contextin (lambda (x) (or (not x) (context? x))))
	    (contextout (lambda (x) (or (not x) (context? x))))))


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
;; Generate s-expressions for the patch egg:
;;
;; ([c|a|d] start-line finish-line new-start-line new-finish-line (lines to be deleted) (lines to be inserted))
;;
;;
(define (diffop->sexp h)

    (cases diffop h
           
	   (Insert (target source seq context)
                   (let ((l (car source)) (r (cdr source)))
                     `(a ,target ,target ,l ,r ,(list) ,seq)))
	   
	   (Remove (target seq context)
                   (let ((l (car target)) (r (cdr target)))
                     `(d ,(+ 1 l) ,r #f #f ,seq ,(list))))

	   (Change (target source seqin seqout contextin contextout)
                   (let ((l (car source)) (r (cdr source))
                         (l1 (car target)) (r1 (cdr target)))
                     `(c ,(+ 1 l1) ,r1 ,(+ 1 l) ,r ,seqout ,seqin)))
	   ))


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
	     (values (make-hunks A B css context-len) A B)))))))




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
	       (elt-slice seq start end))))
       
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

			      ((= 0 x) (cons (Insert x (cons 0 y) (elt-slice B 0 y) 
					       (and context? (cons (list) (make-context B N y (+ y context-len)))))
					       hunks))

			      ((= 0 y) (cons (Remove (cons 0 x) (elt-slice A 0 x)
						       (cons (list) (make-context A M x (+ x context-len))))
					       hunks))

			      (else (cons (Change (cons 0 x) (cons 0 y)
						  (elt-slice B 0 y) (elt-slice A 0 x) 
						  (and context? (cons (list) (make-context B N y (+ y context-len))))
						  (and context? (cons (list) (make-context A M x (+ x context-len)))))
					  hunks)))
			(begin
			  (stack-pop! css)
			  (stack-pop! css)
			  (let-values (((w z) (values x y))
				       ((x y) (psplit2 (stack-peek css))))
                            (let ((newhunk  (cond ((= y z)  
						   (Remove (cons x w) (elt-slice A x w)
							   (and context? 
								(cons (make-context A M (- x context-len) x)
								      (make-context A M x (+ w context-len))))))
						  
						  ((= x w)  
						   (Insert x (cons y z) (elt-slice B y z)
							   (and context? 
								(cons (make-context B N (- y context-len) y)
								      (make-context B N z (+ z context-len))))))

						  (else (Change (cons x w) (cons y z)
								(elt-slice B y z ) (elt-slice A x w)
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
		 (list (Insert 0 (cons 0 N) (elt-slice B 0 N) (and context? `(())))))

		((zero? N) ;; sequence B is empty
		 (list (Remove (cons 0 M) (elt-slice A 0 M)   (and context? `(())))))

		;; the two sequences are completely different
		(else
		 (list (Change (cons 1 M) (cons 1 N)
			       (elt-slice B 0 N)
			       (elt-slice A 0 M)
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
			 (loop css (list (Remove (cons w M) (elt-slice A w M)
						 (and context? (cons (make-context A M w (+ w context-len))
								     (list)))))))

			((= w M)
			 (loop css (list (Insert w (cons z N) (elt-slice B z N)
						 (and context? (cons (make-context B N (- z context-len) z)
								     (list)))))))

			(else (loop css (list (Change (cons w M) (cons z N)
						      (elt-slice B z N )
						      (elt-slice A w M)
						      (and context? (cons (make-context B N (- z context-len) z)
									  (list)))
						      (and context? (cons (make-context A M (- w context-len) w)
									  (list)))
						      )))
			      ))
		  ))
	     ))
      ))
    )


;;
;; Output text diff hunks as ed commands
;;
(define (format-hunks/ed out hunks)

  (define (pair->string p)
    (let ((a (car p)) (b (cdr p)))
      (let ((a (+ 1 a)))
	(if (= a b)
	    (number->string a)
	    (conc a "," b)))))

  (define (format-lines lines out)
    (let ((escape #f))
      (for-each 
       (lambda (l) 
	 (if (string=? l ".")
	     (begin (set! escape #t)
		    (display "..\n.\ns/.//\n" out))
             (for-each (lambda (x) (display x out))
		       (list (if escape
				 (begin 
				   (set! escape #f)
				   "a\n")  
				 "")
			     l "\n") )
             ))
       lines)))
			      

  (define (format hs out)
    (if (not (null? hs))
	(let ((h  (car hs)))
          (cases diffop h
                 (Insert (target source seq context)
                         (begin
                           (display (conc target "a\n") out)
                           (format-lines seq out)
                           (display ".\n" out)))
                 (Remove (target seq context)
                         (begin
                           (display (pair->string target) out)
                           (display "d\n" out)))
		 (Change (target source seqin seqout contextin contextout)
                         (begin
                           (display (pair->string target) out)
                           (display "c\n" out)
                           (format-lines seqin out)
                           (display ".\n" out))))
	  (format (cdr hs) out))))

  (format (reverse hunks) out))

;;
;; normal diff format
;;
(define (format-hunks/normal out hunks)

  (define (pair->string p)
    (let ((a (car p)) (b (cdr p)))
      (let ((a (+ 1 a)))
	(if (= a b)
	    (number->string a)
	    (conc a "," b)))))

  (define (format-lines prefix lines out)
    (for-each (lambda (l) 
		(display prefix out)
		(display l out)
		(display "\n" out))
              lines))
			      
  (define (format h n out)
    (cases diffop h
	   (Insert (target source seq context)
                   (let ((l (car source)) (r (cdr source)))
                     (display target out)
                     (for-each (lambda (x) (display x out))
                               (list "a" (pair->string source) "\n"))
                     (format-lines "> " seq out)
                     (+ n (- r l))))
	   
	   (Remove (target seq context)
                   (let ((l (car target)) (r (cdr target)))
                     (display (pair->string target) out)
                     (display "d" out)
                     (display (+ l n) out)
                     (display "\n" out)
                     (format-lines "< " seq out)
                     (- n (- r l))))
	   
	   (Change (target source seqin seqout contextin contextout)
                   (let ((l (car source)) (r (cdr source))
                         (l1 (car target)) (r1 (cdr target)))
		       (for-each (lambda (x) (display x out))
				 (list (pair->string target)  "c" 
				       (pair->string source) "\n"))
		       (format-lines "< " seqout out)
		       (display "---\n" out)
		       (format-lines "> " seqin out)
		       (+ n (- (- r l) (- r1 l1) ))))
	   ))

  (fold (lambda (h n) (format h n out)) 0 hunks))


;; RCS format
(define (format-hunks/rcs out hunks)

  (define (pair->string p)
    (let ((a (car p)) (b (cdr p)))
      (let ((a (+ 1 a)))
	(if (= a b)
	    (number->string a)
	    (conc a "," b)))))

  (define (format-lines lines out)
    (for-each (lambda (l) 
		(display l out)
		(display "\n" out))
              lines))
			      
  (define (format h out)
    (cases diffop h
	   (Insert (target source seq context)
                   (let ((l (car source)) (r (cdr source)))
                     (for-each (lambda (x) (display x out))
                               (list "a" (number->string target) " "))
                     (display (- r l) out)
                     (display "\n" out)
                     (format-lines seq out)))

	   (Remove (target seq context)
                   (let ((l (car target)) (r (cdr target)))
                     (display "d" out)
                     (display (+ 1 l) out)
                     (display " " out)
                     (display (- r l) out)
                     (display "\n" out)))
	   
	   (Change (target source seqin seqout contextin contextout)
                   (let ((l (car source)) (r (cdr source))
                         (l1 (car target)) (r1 (cdr target)))
                     (display "d" out)
                     (display (+ 1 l) out)
                     (display " " out)
                     (display (- r l) out)
                     (display "\n" out)
                     (display "a" out)
                     (display (+ l (- r l)) out)
                     (display " " out)
                     (display (- r1 l1) out)
                     (display "\n" out)
                     (format-lines seqin out)))))

  (for-each (lambda (h) (format h out)) hunks))



;; Context format (patch)
(define (format-hunks/context out hunks fname1 tstamp1 fname2 tstamp2)

  (define hunkhead  "***************\n")
  (define fromhead "*** ")
  (define fromtail " ****\n")
  (define tohead   "--- ")
  (define totail   " ----\n")

  (define (pair->string p)
    (let ((a (car p)) (b (cdr p)))
      (let ((a (if (< a b) (+ 1 a) a)))
        (if (= a b)
            (number->string a)
            (conc a "," b)))))
 
  ;; compute the line ranges of context hunks
  (define (get-target-range h)
    (cases diffop h
	   (Insert (x source seq context)
                   (let ((before (car context)) (after (cdr context)))
                     (let ((na (+ (or (and after  (size after)) 0) (size seq)))
                           (nb (or (and before (size before)) 0)))
                       (cons (- x nb) (+ x na)))))

	   (Remove (target seq context)
                   (let ((x (car target)) (y (cdr target))
                         (before (car context)) (after (cdr context)))
                     (let ((na (or (and after  (size after)) 0))
                           (nb (or (and before (size before)) 0)))
                       (cons (- x nb) (+ y (max 0 (- na (- y x))))))))

	   (Change (target source datain dataout contextin contextout)
                   (let ((x (car target)) (y (cdr target))
                         (before (car contextout)) (after (cdr contextout)))
                     (let ((na (or (and after  (size after)) 0))
                           (nb (or (and before (size before)) 0)))
                       (cons (- x nb) (+ y na)))))

	   ))

  (define (get-source-range h)
    (cases diffop h
	   (Insert (target source seq context)
                   (let ((x (car source)) (y (cdr source))
                         (before (car context)) (after (cdr context)))
                     (let ((na (or (and after  (size after)) 0))
                           (nb (or (and before (size before)) 0)))
                       (cons (- x nb) (+ y na)))))


	   (Remove (target seq context)
                   (let ((x (car target)) (y (cdr target))
                         (before (car context)) (after (cdr context)))
                     (let ((na (or (and after  (size after)) 0))
                           (nb (or (and before (size before)) 0)))
                       (cons (- x nb) (+ x (max 0 (- na (- y x))))))))


	   (Change (target source datain dataout contextin contextout)
                   (let ((x (car source)) (y (cdr source))
                         (before (car contextin)) (after (cdr contextin)))
                     (let ((na (or (and after  (size after)) 0))
                           (nb (or (and before (size before)) 0)))
                       (cons (- x nb) (+ y na)))))

	   ))

  ;; Counts all lines in v that are not #f
  (define (line-count v) (dynvector-fold (lambda (i state vv) (if vv (+ state 1) state)) 0 v))

  ;; converts a hunk to a vector of lines where each line can be
  ;; prefixed by - + ! or nothing
  (define (hunk->vector h #!key (target-vect #f)  (source-vect #f)
                        (target-range (get-target-range h)) 
                        (source-range (get-source-range h))
                        (target-start #f) (source-start #f))

      (cases diffop h  

	   (Insert (target source data context)
                   (let ((before (car context)) (after (cdr context)))
                     (let ((invect  (or source-vect (make-dynvector (- (cdr source-range) (car source-range)) #f)))
                           (outvect (or target-vect (make-dynvector (+ (size after) (size before)) #f)))
                           (source-start    (or source-start 0))
                           (target-start    (or target-start 0)))

                       (let ((n source-start))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (let ((v (dynvector-ref invect (+ n i))))
                                (cond ((not v)
                                       (dynvector-set! invect i (cons #f s)))
                                      ((and (pair? v) (not (car v)))
                                       (dynvector-set! invect i (cons #f s)))
                                      ))
                              ))
                          before))
                       (let ((n (+ source-start (size before))))
                         (do-items
                          (lambda (item) 
                            (let ((i (car item)) (s (cadr item)))
                              (dynvector-set! invect (+ n i) (cons '+ s))
                              ))
                          data))
                       (let ((n (+ source-start (size before) (size data))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (let ((v (dynvector-ref invect (+ n i))))
                                (cond ((not v)
                                       (dynvector-set! invect (+ n i) (cons #f s)))
                                      ((and (pair? v) (not (car v)))
                                       (dynvector-set! invect (+ n i) (cons #f s)))
                                      ))
                              ))
                          after))
                       (let ((n target-start))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (let ((v (dynvector-ref outvect (+ n i))))
                                (cond ((not v)
                                       (dynvector-set! outvect (+ n i) (cons #f s)))
                                      ((and (pair? v) (not (car v)))
                                       (dynvector-set! outvect (+ n i) (cons #f s)))
                                      ))
                              ))
                          before))
                       (let ((n (+ target-start (size before))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (let ((v (dynvector-ref outvect (+ n i))))
                                (cond ((not v)
                                       (dynvector-set! outvect (+ n i) (cons #f s)))
                                      ((and (pair? v) (not (car v)))
                                       (dynvector-set! outvect (+ n i) (cons #f s)))
                                      ))
                              ))
                          after))

                       (values invect outvect
                               (cons (car source-range) (+ (car source-range) (line-count invect)))
                               (cons (car target-range) (+ (car target-range) (line-count outvect)))
                               )
	      
                       ))
                   )

	   (Remove (target data context)
                   (let ((x (car target)) (y (cdr target))
                         (before (car context)) (after (cdr context)))
                     (let ((invect   (or source-vect (make-dynvector (+ (size after) (size before)) #f)))
                           (outvect  (or target-vect (make-dynvector (- (cdr target-range) (car target-range)) #f)))
                           (start    (or target-start 0)))

                       (let ((n start))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (if (not (dynvector-ref outvect (+ n i)))
                                  (dynvector-set! outvect (+ n i) (cons #f s)))
                              ))
                          before))
                       
                       (let ((n (+ start (size before))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (dynvector-set! outvect i (cons '- s))
                              ))
                          data))
                       
                       (let ((n (- (+ start (+ (size data) (size before))) 1)))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (if (not (dynvector-ref outvect (+ n i)))
                                  (dynvector-set! outvect (+ n i) (cons #f s)))))
                          after))

                       (let ((nb (size before)))
                           (if before
                               (let ((n (if (>= start nb) (- start nb) start)))
                                 (do-items
                                  (lambda (item)
                                    (let ((i (car item)) (s (cadr item)))
                                      (let ((v (dynvector-ref outvect (+ i n))))
                                        (if (not (dynvector-ref invect (+ i n)))
                                            (if (case (car v) ((+ ! #f) #t) (else #f))
                                                (dynvector-set! invect (+ i n) (cons #f s)))
                                            ))
                                      ))
                                  before))
                               ))

                       (let ((nd (- y x))
                             (n  (+ start (size after))))
                         (let loop ((i (+ 1 start)) (j (+ 1 (+ nd start))))
                           (let ((v (dynvector-ref outvect j)))
                             (if (and (not (dynvector-ref invect i)) v
                                      (case (car v) ((+ ! #f) #t) (else #f)))
                                 (dynvector-set! invect i (cons #f (cdr v))))
                             (if (<= i n) (loop (+ 1 i) (+ 1 j) ))
                             )))
                       
                       (values invect outvect
                               (cons (car source-range) (+ (car source-range) (line-count invect)))
                               (cons (car target-range) (+ (car target-range) (line-count outvect))))
                       ))
                   )
	   
           (Change (target source datain dataout contextin contextout)
                   (let ((x (car target)) (y (cdr target))
                         (w (car source)) (z (cdr source))
                         (beforein (car contextin)) (afterin (cdr contextin))
                         (beforeout (car contextout)) (afterout (cdr contextout)))

                     (let ((outvect  (or target-vect (make-dynvector (- (cdr target-range) (car target-range)) #f)))
                           (invect   (or source-vect (make-dynvector (- (cdr source-range) (car source-range)) #f)))
                           (outstart (or target-start 0))
                           (instart  (or source-start 0)))

                       (let ((n outstart))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (if (not (dynvector-ref outvect i))
                                  (dynvector-set! outvect (+ n i) (cons #f s)))))
                          beforeout))
                       (let ((n (+ outstart (size beforeout))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (dynvector-set! outvect (+ n i) (cons '! s))))
                          dataout))
                       (let ((n (+ outstart (+ (size dataout) (size beforeout)))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (if (not (dynvector-ref outvect i))
                                  (dynvector-set! outvect (+ n i) (cons #f s)))))
                          afterout))
                       (let ((n instart))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (if (not (dynvector-ref invect i))
                                  (dynvector-set! invect (+ n i) (cons #f s)))))
                          beforein))
                       (let ((n (+ instart (size beforein))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (dynvector-set! invect (+ n i) (cons '! s)) ))
                          datain))
                       (let ((n (+ instart (size datain) (size beforein))))
                         (do-items
                          (lambda (item)
                            (let ((i (car item)) (s (cadr item)))
                              (if (not (dynvector-ref invect i))
                                  (dynvector-set! invect i (cons #f s)))))
                          afterin))

                       (values invect outvect source-range target-range)))
                   )
	   ))

  ;; checks if hunk ranges overlap or are adjacent
  (define (adjacent? range1 range2)
    (and (and range1 range2)
	 (>= 0 (- (car range2) (cdr range1)))))

  ;; incorporates hunk h into the given source/target vectors
  (define (merge h target-vect source-vect target-range source-range)

    (let ((h-target-range (get-target-range h))
	  (h-source-range (get-source-range h)))

      (hunk->vector h target-vect: target-vect source-vect: source-vect 

		    ;; merge the ranges
		    target-range:
                    (let ((target-range
			   (cond ((and target-range h-target-range) 
				  (cons (min (car target-range) (car h-target-range))
					(max (cdr target-range) (cdr h-target-range))))
				 (target-range target-range)
				 (h-target-range h-target-range)
				 (else (error "context diff merge: invalid target range")))))
		      target-range)

                    source-range:
		    (let ((source-range
			   (cond ((and source-range h-source-range)
				  (cons (min (car source-range) (car h-source-range))
					(max (cdr source-range) (cdr h-source-range))))
				 (source-range source-range)
				 (h-source-range h-source-range)
				 (else (error "context diff merge: invalid source range")))))
		      source-range)

		    ;; determine start index
		    target-start:
                    (and h-target-range target-range
			 (let ((hx  (car h-target-range))
			       (x   (car target-range)))
			   (and (> hx x) (- hx x))))

                    source-start:
		    (and h-source-range source-range 
			 (let ((hx  (car h-source-range))
			       (x   (car source-range)))
			   (and (> hx x) (- hx x))))
                    ))
    )
  
  (define (format source-vect target-vect source-range target-range out)

    (let ((target-vect-change?  
	   (and target-vect (dynvector-any (lambda (x) (and x (car x))) target-vect)))
	  (source-vect-change?  
	   (and source-vect (dynvector-any (lambda (x) (and x (car x))) source-vect))))

      (cond ((and source-vect-change? target-vect-change?)
	     ;; change hunk
	     (display hunkhead out)
	     (display fromhead out)
	     (display (pair->string target-range) out)
	     (display fromtail out)
	     (dynvector-for-each (lambda (i l) 
				   (if l
				       (let ((p (car l)))
					 (display (conc (or p " ") " ") out)
					 (display (cdr l) out)
					 (display "\n" out))))
				 target-vect)
	     (display tohead out)
	     (display (pair->string source-range) out)
	     (display totail out)
	     (dynvector-for-each (lambda (i l) 
				   (if l 
				       (let ((p (car l)))
					 (display (conc (or p " ") " ") out)
					 (display (cdr l) out)
					 (display "\n" out))
				       ))
				 source-vect))
	    
	    (target-vect-change?
	     ;; remove hunk
	     (display hunkhead out)
	     (display fromhead out)
	     (display (pair->string target-range) out)
	     (display fromtail out)
	     (dynvector-for-each (lambda (i l) 
				   (if l
				       (let ((p (car l)))
					 (display (conc (or p " ") " ") out)
					 (display (cdr l) out)
					 (display "\n" out))
				       ))
				 target-vect)
	     (display tohead out)
	     (display (pair->string source-range) out)
	     (display totail out))

	    (source-vect-change?
	     ;; insert hunk
	     (display hunkhead out)
	     (display fromhead out)
	     (display (pair->string target-range) out)
	     (display fromtail out)
	     (display tohead out)
	     (display (pair->string source-range) out)
	     (display totail out)
	     (dynvector-for-each (lambda (i l) 
				   (let ((p (car l)))
				     (display (conc (or p " ") " ") out)
				     (display (cdr l) out)
				     (display "\n" out)))
				 source-vect))
	    
            ))
    )

  (begin
    
   (for-each (lambda (x) (display x out)) (list fromhead fname1 " " tstamp1 "\n"))
   (for-each (lambda (x) (display x out)) (list tohead fname2 " " tstamp2 "\n"))
  
   (if (not (null? hunks))
       (let-values (((source-vect target-vect source-range target-range)
                     (hunk->vector (car hunks))))
         
         (let loop ((hunks         (cdr hunks))
                    (source-vect   source-vect)
                    (target-vect   target-vect)
                    (source-range  source-range)
                    (target-range  target-range))
           
           (if (null? hunks)
               
               (format source-vect target-vect source-range target-range out)
               
               (let* ((h (car hunks))
                      (h-target-range (get-target-range h)))
                 
                 (if (adjacent? target-range h-target-range)
                     
                     ;; merge contiguous hunks and recurse
                     (let-values (((source-vect1 target-vect1 source-range1 target-range1)
                                   (merge h target-vect source-vect target-range source-range)))
                       (loop (cdr hunks)
                             source-vect1 target-vect1
                             source-range1 target-range1))
                     
                     ;; print current hunk and recurse
                     (let-values (((source-vect1 target-vect1 source-range1 target-range1)
                                   (hunk->vector h)))
                       (format source-vect target-vect source-range target-range out)
                       (loop (cdr hunks) source-vect1 target-vect1 source-range1 target-range1)))
                 ))
           ))
       ))
  )

)
