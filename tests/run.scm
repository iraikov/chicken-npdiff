(import scheme ( chicken base) (chicken io) (chicken port) npdiff test)



(test-group "empty input sequences"

   (let ((empty (with-input-from-string "" read-lines))
	 (abc (with-input-from-string "abc" read-lines)))
       (print (npdiff empty abc 3))
       (print (npdiff abc empty 3))
       
       )
   )

(test-group "text1 -> text2"

   (let ((text1 (call-with-input-file "tests/text1" read-lines))
	 (text2 (call-with-input-file "tests/text2" read-lines)))
       (print (npdiff text1 text2 3))
       (print (npdiff text2 text1 3))
       
       )
   )

(test-group "pointers1 -> pointers2"

   (let ((pointers1 (call-with-input-file "tests/pointers1" read-lines))
	 (pointers2 (call-with-input-file "tests/pointers2" read-lines)))
       (print (npdiff pointers1 pointers2 3))
       (print (npdiff pointers2 pointers1 3))
       
       )
   )

(test-group "large0 -> large1"

   (let ((large0 (call-with-input-file "tests/large0" read-lines))
	 (large1 (call-with-input-file "tests/large1" read-lines)))
       (print (npdiff large0 large1 3))
       (print (npdiff large0 large1 3))
       
       )
   )


(test-group "format empty input sequences"

   (let ((empty (with-input-from-string "" read-lines))
	 (abc (with-input-from-string "abc" read-lines)))
     (let ((hunks1 (npdiff empty abc 3))
	   (hunks2 (npdiff abc empty 3)))

       (call-with-output-string
		    (lambda (out) (format-hunks/context out hunks1
                                                        "empty" "" "abc" "")))
       
       (test-group "diff empty -> abc"
		   (test "normal format" 
#<<EOF
0a1
> abc

EOF
                   (call-with-output-string
		    (lambda (out) (format-hunks/normal out hunks1))))
		   (test "ed format"
#<<EOF
0a
abc
.

EOF
                   (call-with-output-string
		    (lambda (out) (format-hunks/ed out hunks1))))
		   (test "rcs format"
#<<EOF
a0 1
abc

EOF
                   (call-with-output-string
		    (lambda (out) (format-hunks/rcs out hunks1))))
		   (test "context format"
#<<EOF
*** empty 
--- abc 
***************
*** 0 ****
--- 1 ----
+ abc

EOF
                   (call-with-output-string
		    (lambda (out) (format-hunks/context out hunks1
				   "empty" "" "abc" ""))))
		   ))
     ))

(test-exit)
