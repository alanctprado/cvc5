(set-logic ALL)
(set-info :status unsat)
(declare-fun x () (_ BitVec 32))
(declare-fun y () Int)

(assert (or
(< (ubv_to_int x) 0)
(<= (ubv_to_int x) (- 1))
(>= (ubv_to_int x) 4294967296)
(> (ubv_to_int x) 4294967295)
(and (not (= (mod y 4294967296) 4294967295)) (bvuge ((_ int_to_bv 32) y) #xFFFFFFFF))
(bvult ((_ int_to_bv 32) y) #x00000000)
(bvugt ((_ int_to_bv 32) y) #xFFFFFFFF)
(and (not (= (mod y 4294967296) 0)) (bvule ((_ int_to_bv 32) y) #x00000000))
))
(check-sat)
