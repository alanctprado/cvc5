(set-logic QF_BV)

(declare-const x (_ BitVec DOUBLE))
(declare-const x_temp (_ BitVec SIZE))
(assert (= x ((_ zero_extend SIZE) x_temp)))

(declare-const k (_ BitVec DOUBLE))
(declare-const k_temp (_ BitVec SIZE))
(assert (= k ((_ zero_extend SIZE) k_temp)))

(declare-const z (_ BitVec DOUBLE))
(declare-const z_temp (_ BitVec SIZE))
(assert (= z ((_ zero_extend SIZE) z_temp)))

(assert (= k_temp #bCONSTANT))

(assert
	(bvult
		(bvmul k z)
		(bvmul (bvand x k) z)
	)
)

(check-sat)
