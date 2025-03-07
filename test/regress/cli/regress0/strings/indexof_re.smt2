; COMMAND-LINE:
(set-logic QF_SLIA)
(declare-const x String)
(assert (or
  (not (= (str.indexof_re "abc" re.allchar (- 1)) (- 1)))
  (not (= (str.indexof_re "abc" re.allchar (- 2)) (- 1)))
  (not (= (str.indexof_re "abc" re.allchar 5) (- 1)))
  (not (= (str.indexof_re "abc" re.allchar 0) 0))
  (not (= (str.indexof_re "abc" re.allchar 1) 1))
  (not (= (str.indexof_re "abc" re.allchar 2) 2))
  (not (= (str.indexof_re "abc" re.allchar 3) (- 1)))
  (not (= (str.indexof_re "abc" (re.++ re.allchar re.allchar) 2) (- 1)))
  (not (= (str.indexof_re "abc" (re.union (str.to_re "") re.allchar) 3) 3))
  (not (= (str.indexof_re (str.++ "abc" x) (re.union (str.to_re "") re.allchar) 3) 3))
  (not (= (str.indexof_re "cbabc" (re.union (str.to_re "a") (str.to_re "bab")) 0) 1))
))
(set-info :status unsat)
(check-sat)
