; COMMAND-LINE: --arrays-exp --ee-mode=distributed
; COMMAND-LINE: --arrays-exp --ee-mode=central
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-datatypes ((r 0)) (((R1 (x1 Int)))))
(declare-datatype t ((M (t1 (Array Int Int)) (t2 (Array Int Int)))))
(declare-datatypes ((q 0)) (((R (x (Array Int r)) (y t)))))
(declare-fun z () q)
(assert (= z (R ((as const (Array Int r)) (R1 0)) (M ((as const (Array Int Int)) 1) ((as const (Array Int Int)) 0)))))
(assert (= (x1 (select (x z) 0)) (select (t1 (y z)) 1)))
(check-sat)
