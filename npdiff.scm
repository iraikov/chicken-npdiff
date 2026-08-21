
;;
;; Compute the longest common subsequence of two sequences 
;;
;; Copyright 2007-2026 Ivan Raikov.
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
         hunks->sexp
         format-hunks/normal
         format-hunks/ed
         format-hunks/rcs
         format-hunks/context
         )
		   
 (import scheme (chicken base) (chicken string) (chicken sort) srfi-1 srfi-4 datatype
         yasos (except yasos-collections sort sort!) iset)


 

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


(set-record-printer! diffop
 (lambda (x out)
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
			 (display ")" out)))))

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
                     `(a ,target ,target ,(+ 1 l) ,r ,(list) ,seq)))
	   
	   (Remove (target seq context)
                   (let ((l (car target)) (r (cdr target)))
                     `(d ,(+ 1 l) ,r #f #f ,seq ,(list))))

	   (Change (target source seqin seqout contextin contextout)
                   (let ((l (car source)) (r (cdr source))
                         (l1 (car target)) (r1 (cdr target)))
                     `(c ,(+ 1 l1) ,r1 ,(+ 1 l) ,r ,seqout ,seqin)))
	   ))

;; Like diffop->sexp, but converts a whole hunk list in one pass so
;; that Remove entries can carry a real B-line position instead of #f.
;; A Remove hunk has no B-side data of its own, but reverse-patch
;; (from the patch egg) needs a B-position in order to turn the removal
;; into a well-formed insertion when reversing, so this threads
;; the running B-A delta across the hunks (the same quantity
;; format-hunks/normal folds over) to compute it.
;; Insert and Change already carry real B-coordinates in their own
;; `source` field, so their sexps are unchanged from diffop->sexp.
(define (hunks->sexp hunks)
  (let loop ((hunks hunks) (delta 0) (acc (list)))
    (if (null? hunks) (reverse acc)
        (let ((h (car hunks)))
          (cases diffop h
                 (Remove (target seq context)
                         (let* ((l (car target)) (r (cdr target))
                                (b (+ l delta)))
                           (loop (cdr hunks) (- delta (- r l))
                                 (cons `(d ,(+ 1 l) ,r ,b ,b ,seq ,(list)) acc))))
                 (Insert (target source seq context)
                         (loop (cdr hunks) (+ delta (- (cdr source) (car source)))
                               (cons (diffop->sexp h) acc)))
                 (Change (target source seqin seqout contextin contextout)
                         (loop (cdr hunks)
                               (+ delta (- (- (cdr source) (car source))
                                           (- (cdr target) (car target))))
                               (cons (diffop->sexp h) acc))))))))


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
								      (make-context A M w (+ w context-len))))))
						  
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
		 (list (Change (cons 0 M) (cons 0 N)
			       (elt-slice B 0 N)
			       (elt-slice A 0 M)
			       (and context? (cons (list) (list)))
			       (and context? (cons (list) (list))))))
		)

	  (let-values (((endpair startpair)  (stack-ppeek css)))
	     (let ((k (stack-depth css)))
		(let-values (((x y)  (psplit2 startpair))
			     ((w z)  (psplit2 endpair)))

                  (cond ((and (= w M) (= z N))

			 (loop css (list)))

			((= z N)
			 (loop css (list (Remove (cons w M) (elt-slice A w M)
						 (and context? (cons (make-context A M (- w context-len) w)
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
;;
;; run: a maximal span of consecutive integers in the merged iset.
;; A run is just an interval (lo . hi) that has no knowledge of
;; which hunks produced it.
;;
;; block: the list of hunks assigned to one run. Runs and blocks are
;; in 1:1 correspondence, but a run is a pair of integers while a
;; block is a list of hunks.
;;
;; Algorithm (interval-union with padding):
;;
;;   1. DILATE     Pad each hunk's target range (A line coordinates) by its
;;                 own before/after context size, producing one interval
;;                 per hunk.
;;   2. MERGE      Union the dilated intervals in an iset. iset does
;;                 the actual merging; the maximal runs of the result
;;                 are the final block boundaries.
;;   3. PARTITION  Assign each hunk to the block (run) its dilated
;;                 interval falls into.
;;   4. PRINT      For each block, in order:
;;        a. its A-range is read directly off its first/last hunk
;;           (dilated-lo/dilated-hi);
;;        b. its B-range is derived from a running insert/delete
;;           delta, threaded block to block (the same quantity
;;           format-hunks/normal already folds over);
;;        c. the block is rendered by walking its hunks and the gaps
;;           between them, printing shared context text once (a
;;           context line is the same text on both sides) and each
;;           hunk's own marked lines, separately for the "***" (A) and
;;           "---" (B) sides.
;;
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

  ;; target is always A-line coordinates, for all three variants
  (define (hunk-target-range h)
    (cases diffop h
	   (Insert (target source seq context) (cons target target))
	   (Remove (target seq context) target)
	   (Change (target source datain dataout contextin contextout) target)))

  ;; width of what this hunk contributes on the B side; 0 for Remove,
  ;; which has no B-side representation at all
  (define (hunk-source-width h)
    (cases diffop h
	   (Insert (target source seq context) (- (cdr source) (car source)))
	   (Remove (target seq context) 0)
	   (Change (target source datain dataout contextin contextout) (- (cdr source) (car source)))))

  ;; (before . after) context around the hunk. Context lines are common
  ;; to both files, so this single pair is used for both the "***" and
  ;; "---" blocks regardless of which sequence it happens to be sliced
  ;; from.
  (define (hunk-context h)
    (cases diffop h
	   (Insert (target source seq context) context)
	   (Remove (target seq context) context)
	   (Change (target source datain dataout contextin contextout) contextout)))

  ;; (marker . lines) shown on the "***" (A) side, or #f for Insert
  ;; (which touches only B)
  (define (hunk-target-marked h)
    (cases diffop h
	   (Insert (target source seq context) #f)
	   (Remove (target seq context) (cons '- seq))
	   (Change (target source datain dataout contextin contextout) (cons '! dataout))))

  ;; (marker . lines) shown on the "---" (B) side, or #f for Remove
  (define (hunk-source-marked h)
    (cases diffop h
	   (Insert (target source seq context) (cons '+ seq))
	   (Remove (target seq context) #f)
	   (Change (target source datain dataout contextin contextout) (cons '! datain))))

  ;; step 1 (DILATE): a hunk's target range, padded by its own (already
  ;; boundary-clipped) before/after context sizes
  (define (dilated-lo h) (- (car (hunk-target-range h)) (size (car (hunk-context h)))))
  (define (dilated-hi h) (+ (cdr (hunk-target-range h)) (size (cdr (hunk-context h)))))

  (define (print-lines marker coll out)
    (do-elts (lambda (s)
	       (display (conc (or marker " ") " ") out)
	       (display s out)
	       (display "\n" out))
	     coll))

  ;; step 2 (MERGE) helper: iset only exposes element-level iteration,
  ;; so maximal runs are recovered by scanning the sorted member list
  ;; for consecutive spans
  (define (iset->runs is)
    (let loop ((members (sort (iset->list is) <)) (runs '()))
      (if (null? members) (reverse runs)
	  (let scan ((rest (cdr members)) (lo (car members)) (hi (+ 1 (car members))))
	    (if (and (pair? rest) (= (car rest) hi))
		(scan (cdr rest) lo (+ 1 hi))
		(loop rest (cons (cons lo hi) runs)))))))

  ;; steps 1-3 (DILATE, MERGE, PARTITION): each hunk contributes its
  ;; dilated interval (at least 1 wide, so a hunk with empty context on
  ;; both sides still registers a point to merge/print around) to an
  ;; iset; iset-union performs the merge; the resulting runs are read
  ;; back to partition the hunks into blocks.
  (define (merge-hunks hunks)
    (let ((dilated
	   (fold (lambda (h is)
		   (let* ((lo (dilated-lo h))
			  (hi (max (dilated-hi h) (+ lo 1))))
		     (iset-union is (make-iset lo (- hi 1)))))
		 (make-iset)
		 hunks)))
      (let loop ((hunks hunks) (runs (iset->runs dilated)) (blocks '()))
	(if (null? runs) (reverse blocks)
	    (let-values (((this rest)
			  (span (lambda (h) (< (dilated-lo h) (cdr (car runs)))) hunks)))
	      (loop rest (cdr runs) (cons this blocks)))))))

  ;; step 4c (PRINT) helper: content of the gap between two hunks (or
  ;; between a block boundary and its first/last hunk, when prev-h/
  ;; next-h is #f). A gap can be wider than either neighbor's own
  ;; context window alone, since two hunks only merge
  ;; into one block when their windows together cover the gap between
  ;; them, so this takes as much as it can from the left
  ;; (prev-h's after-context) and the rest
  ;; from the right (next-h's before-context).
  (define (gap-content prev-h next-h width)
    (let ((after  (and prev-h (cdr (hunk-context prev-h))))
	  (before (and next-h (car (hunk-context next-h)))))
      (cond ((not prev-h) (elt-slice before (max 0 (- (size before) width)) (size before)))
	    ((not next-h)  (elt-slice after 0 (min width (size after))))
	    (else
	     (let ((n1 (min (size after) width)))
	       (append (elt-slice after 0 n1)
		       (elt-slice before (max 0 (- (size before) (- width n1))) (size before))))))))

  ;; step 4c (PRINT): walks the gaps and hunks of one block, printing
  ;; shared context text between them and each hunk's own marked
  ;; content (target- or source-side, selected via get-marked)
  (define (print-run-side block run-lo run-hi get-marked out)
    (let loop ((hs block) (prev-end run-lo) (prev-h #f))
      (if (null? hs)
	  (print-lines #f (gap-content prev-h #f (- run-hi prev-end)) out)
	  (let* ((h (car hs)) (tr (hunk-target-range h)) (lo (car tr)))
	    (print-lines #f (gap-content prev-h h (- lo prev-end)) out)
	    (let ((marked (get-marked h)))
	      (if marked (print-lines (car marked) (cdr marked) out)))
	    (loop (cdr hs) (cdr tr) h)))))

  ;; step 4 (PRINT): computes one block's A-range (4a) and B-range
  ;; (4b), renders both sides (4c), and returns the running B-A delta
  ;; for the next block's B-range (4b) to build on
  (define (print-block block delta-before out)
    (let* ((h1 (car block))
	   (hk (car (reverse block)))
	   (a-lo (dilated-lo h1))                          ; 4a
	   (a-hi (dilated-hi hk))                           ; 4a
	   (b-lo (+ a-lo delta-before))                     ; 4b
	   (delta-after
	    (fold (lambda (h d)
		    (let ((tr (hunk-target-range h)))
		      (+ d (- (hunk-source-width h) (- (cdr tr) (car tr))))))
		  delta-before block))
	   (b-hi (+ a-hi delta-after)))                     ; 4b

      (display hunkhead out)
      (display fromhead out) (display (pair->string (cons a-lo a-hi)) out) (display fromtail out)
      ;; a side's body is only shown when the block actually marks a
      ;; changed line on that side; a block made up entirely of
      ;; Inserts (or entirely of Removes) leaves the other side's
      ;; header with no body at all, matching diff -c
      (if (any hunk-target-marked block)
	  (print-run-side block a-lo a-hi hunk-target-marked out))
      (display tohead out) (display (pair->string (cons b-lo b-hi)) out) (display totail out)
      (if (any hunk-source-marked block)
	  (print-run-side block a-lo a-hi hunk-source-marked out))

      delta-after))

  ;; driver: file headers, then steps 1-3 (merge-hunks) followed by
  ;; step 4 (print-block) for each resulting block in turn, threading
  ;; the running B-A delta (4b) from one block to the next
  (begin
    (for-each (lambda (x) (display x out)) (list fromhead fname1 " " tstamp1 "\n"))
    (for-each (lambda (x) (display x out)) (list tohead fname2 " " tstamp2 "\n"))
    (fold (lambda (block delta) (print-block block delta out))
	  0
	  (merge-hunks hunks)))
  )

)
