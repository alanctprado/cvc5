(set-logic QF_BV)

(declare-const x (_ BitVec 20))
(declare-const k (_ BitVec 20))
(declare-const z (_ BitVec 20))

(assert (= k #b10101010101010101010))

(assert
	(bvult
		(bvmul k z)
		(bvmul (bvand x k) z)
	)
)

(check-sat)
