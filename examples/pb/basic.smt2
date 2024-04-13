(set-logic QF_BV)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))

(assert (bvult (_ bv0 4) x))

(assert (bvult x (_ bv4 4)))

(assert (bvult y (_ bv8 4)))
(assert (bvult (_ bv0 4) y))

(assert (= (bvadd x y) (_ bv0 4)))

(check-sat)
