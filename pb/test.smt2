(set-logic QF_BV)

(declare-const x (_ BitVec 16))
(declare-const x_temp (_ BitVec 8))
(assert (= x ((_ zero_extend 8) x_temp)))

(declare-const k (_ BitVec 16))
(declare-const k_temp (_ BitVec 8))
(assert (= k ((_ zero_extend 8) k_temp)))

(declare-const z (_ BitVec 16))
(declare-const z_temp (_ BitVec 8))
(assert (= z ((_ zero_extend 8) z_temp)))

(assert (= k_temp #b10101010))

(assert
	(bvult
		(bvmul k z)
		(bvmul (bvand x k) z)
	)
)

(check-sat)
