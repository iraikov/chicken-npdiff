(import scheme (chicken base) (chicken io) (chicken port) srfi-1 npdiff test)

(define (read-file-lines path) (call-with-input-file path read-lines))

(define (normal-string a b context-len)
  (call-with-output-string (lambda (out) (format-hunks/normal out (npdiff a b context-len)))))

(define (ed-string a b context-len)
  (call-with-output-string (lambda (out) (format-hunks/ed out (npdiff a b context-len)))))

(define (rcs-string a b context-len)
  (call-with-output-string (lambda (out) (format-hunks/rcs out (npdiff a b context-len)))))

(define (context-string a b context-len name1 name2)
  (call-with-output-string
   (lambda (out) (format-hunks/context out (npdiff a b context-len) name1 "" name2 ""))))

(test-group "empty sequences"
  (test "empty vs empty produces no hunks" '() (npdiff '() '() 3))
  (test "identical sequences produce no hunks" '() (npdiff '("a" "b" "c") '("a" "b" "c") 3))

  (test "empty A, non-empty B is a single Insert"
        '((a 0 0 1 2 () ("a" "b")))
        (map diffop->sexp (npdiff '() '("a" "b") 3)))

  (test "non-empty A, empty B is a single Remove"
        '((d 1 2 #f #f ("a" "b") ()))
        (map diffop->sexp (npdiff '("a" "b") '() 3)))

  (test "empty A, non-empty B normal format"
        "0a1,2\n> a\n> b\n"
        (normal-string '() '("a" "b") 3))

  (test "non-empty A, empty B normal format"
        "1,2d0\n< a\n< b\n"
        (normal-string '("a" "b") '() 3))

  (test "empty A, non-empty B context format"
        "*** A \n--- B \n***************\n*** 0 ****\n--- 1,2 ----\n+ a\n+ b\n"
        (context-string '() '("a" "b") 3 "A" "B"))

  (test "non-empty A, empty B context format"
        "*** A \n--- B \n***************\n*** 1,2 ****\n- a\n- b\n--- 0 ----\n"
        (context-string '("a" "b") '() 3 "A" "B")))

(test-group "completely disjoint sequences"
  ;; Regression test: make-hunks used to emit a 1-indexed target/source
  ;; pair here (every other branch is 0-indexed), and context that
  ;; captured the *entire* opposite sequence instead of the empty
  ;; context appropriate for a hunk spanning the whole comparison.
  (test "normal format"
        "1,2c1,2\n< x\n< y\n---\n> p\n> q\n"
        (normal-string '("x" "y") '("p" "q") 3))

  (test "context format"
        "*** A \n--- B \n***************\n*** 1,2 ****\n! x\n! y\n--- 1,2 ----\n! p\n! q\n"
        (context-string '("x" "y") '("p" "q") 3 "A" "B")))

;; context-len=2, two single-line changes with a run of "x"s between
;; them: hunks merge into one context block exactly when the gap is
;; <= 2*context-len, and stay separate one line beyond that.
(test-group "context-diff merge boundary"
  (define (bracketed gap)
    (values (append (list "a1") (make-list gap "x") (list "a2"))
            (append (list "b1") (make-list gap "x") (list "b2"))))

  (let-values (((a b) (bracketed 4)))
    (test "gap exactly 2*context-len merges into one block"
          "*** A \n--- B \n***************\n*** 1,6 ****\n! a1\n  x\n  x\n  x\n  x\n! a2\n--- 1,6 ----\n! b1\n  x\n  x\n  x\n  x\n! b2\n"
          (context-string a b 2 "A" "B")))

  (let-values (((a b) (bracketed 5)))
    (test "gap one more than 2*context-len stays two blocks"
          "*** A \n--- B \n***************\n*** 1,3 ****\n! a1\n  x\n  x\n--- 1,3 ----\n! b1\n  x\n  x\n***************\n*** 5,7 ****\n  x\n  x\n! a2\n--- 5,7 ----\n  x\n  x\n! b2\n"
          (context-string a b 2 "A" "B")))

  (let* ((mid (make-list 4 "x"))
         (a (append (list "a1") mid (list "a2") mid (list "a3")))
         (b (append (list "b1") mid (list "b2") mid (list "b3"))))
    (test "three hunks each at the merge boundary collapse into one block"
          "*** A \n--- B \n***************\n*** 1,11 ****\n! a1\n  x\n  x\n  x\n  x\n! a2\n  x\n  x\n  x\n  x\n! a3\n--- 1,11 ----\n! b1\n  x\n  x\n  x\n  x\n! b2\n  x\n  x\n  x\n  x\n! b3\n"
          (context-string a b 2 "A" "B"))))

(test-group "single middle change"
  (let ((a '("a" "b" "c")) (b '("a" "x" "c")))

    (test "normal format"
          "2c2\n< b\n---\n> x\n"
          (normal-string a b 1))

    (test "ed format"
          "2c\nx\n.\n"
          (ed-string a b 1))

    (test "rcs format"
          "d2 1\na2 1\nx\n"
          (rcs-string a b 1))

    (test "context format"
          "*** A \n--- B \n***************\n*** 1,3 ****\n  a\n! b\n  c\n--- 1,3 ----\n  a\n! x\n  c\n"
          (context-string a b 1 "A" "B"))

    (test "diffop->sexp"
          '((c 2 2 2 2 ("b") ("x")))
          (map diffop->sexp (npdiff a b 0)))))

(test-group "diff empty -> abc"
  (let ((hunks1 (npdiff '() '("a" "b" "c") 3)))

    (test "normal format"
          "0a1,3\n> a\n> b\n> c\n"
          (call-with-output-string (lambda (out) (format-hunks/normal out hunks1))))

    (test "ed format"
          "0a\na\nb\nc\n.\n"
          (call-with-output-string (lambda (out) (format-hunks/ed out hunks1))))

    (test "rcs format"
          "a0 3\na\nb\nc\n"
          (call-with-output-string (lambda (out) (format-hunks/rcs out hunks1))))

    (test "context format"
          "*** empty \n--- abc \n***************\n*** 0 ****\n--- 1,3 ----\n+ a\n+ b\n+ c\n"
          (call-with-output-string
           (lambda (out) (format-hunks/context out hunks1 "empty" "" "abc" ""))))))

;; text1 -> text2 exercises an Insert, a Change and a Remove that all
;; get merged into a single context hunk.
(test-group "text1 -> text2 (multi-hunk merge)"
  (let ((text1 (read-file-lines "text1"))
        (text2 (read-file-lines "text2")))

    (test "normal format"
          "0a1\n> w\n3,4c4,6\n< c\n< d\n---\n> x\n> y\n> z\n6,7d7\n< f\n< g\n"
          (normal-string text1 text2 3))

    (test "context format"
          "*** text1 \n--- text2 \n***************\n*** 1,7 ****\n  a\n  b\n! c\n! d\n  e\n- f\n- g\n--- 1,7 ----\n+ w\n  a\n  b\n! x\n! y\n! z\n  e\n"
          (context-string text1 text2 3 "text1" "text2"))))

;; pointers1 -> pointers2 exercises a Remove/Change/Remove chain where
;; the removed line leaves a genuine gap in the pseudo-source table.
(test-group "pointers1 -> pointers2 (multi-hunk merge with removed-line gap)"
  (let ((pointers1 (read-file-lines "pointers1"))
        (pointers2 (read-file-lines "pointers2")))

    (test "normal format"
          "7d6\n< <li><a href=\"100share/filer/base/filer.html\">Filer (without login)</a></li>\n9c8\n< <li><a href=\"100share/waitlesql/base/waitlesql_query.html\">WaitleSQL</a></li>\n---\n> <li><a href=\"100share/filer/base/filer.html\">Filer (without login)</a></li>\n14d12\n< \n"
          (normal-string pointers1 pointers2 3))

    (test "context format"
          "*** pointers1 \n--- pointers2 \n***************\n*** 4,17 ****\n  here is some useful pointers.\n  \n  <ul>\n- <li><a href=\"100share/filer/base/filer.html\">Filer (without login)</a></li>\n  <li><a href=\"AUTH/100share/filer/base/filer.html\">Filer (with login)</a></li>\n! <li><a href=\"100share/waitlesql/base/waitlesql_query.html\">WaitleSQL</a></li>\n  </ul>\n  \n  Have fun!!!\n  \n- \n  </body>\n  </html>\n  \n--- 4,15 ----\n  here is some useful pointers.\n  \n  <ul>\n  <li><a href=\"AUTH/100share/filer/base/filer.html\">Filer (with login)</a></li>\n! <li><a href=\"100share/filer/base/filer.html\">Filer (without login)</a></li>\n  </ul>\n  \n  Have fun!!!\n  \n  </body>\n  </html>\n  \n"
          (context-string pointers1 pointers2 3 "pointers1" "pointers2"))))

;; large0 -> large1 is a real-world-sized C source diff. npdiff's O(NP)
;; algorithm can pick a different (but equally valid) alignment than
;; GNU diff when several common subsequences of the same length exist,
;; so this is a basic functionality test rather than a byte-for-byte
;; comparison against an external diff tool.
(test-group "large0 -> large1 (basic functionality test)"
  (let ((large0 (read-file-lines "large0"))
        (large1 (read-file-lines "large1")))

    (test-assert "produces at least one hunk"
                 (pair? (npdiff large0 large1 3)))

    (test-assert "normal format runs without error"
                 (string? (normal-string large0 large1 3)))

    (test-assert "context format runs without error"
                 (string? (context-string large0 large1 3 "large0" "large1")))

    (test-assert "ed format runs without error"
                 (string? (ed-string large0 large1 3)))

    (test-assert "rcs format runs without error"
                 (string? (rcs-string large0 large1 3)))))

(test-exit)
