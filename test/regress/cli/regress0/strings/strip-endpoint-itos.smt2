(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)

(set-info :status sat)
(declare-fun x () Int)
(assert (str.contains "Ducati100" (str.from_int x)))
(check-sat)
