; EXPECT: unsat
(set-logic ALL)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (bvult 
(let ((u1 (bvadd x y)))
(let ((u2 (bvand u1 u1)))
(let ((u3 (bvadd u2 u2)))
(let ((u4 (bvand u3 u3)))
(let ((u5 (bvadd u4 u4)))
(let ((u6 (bvand u5 u5)))
(let ((u7 (bvadd u6 u6)))
(let ((u8 (bvand u7 u7)))
(let ((u9 (bvadd u8 u8)))
(let ((u10 (bvand u9 u9)))
(let ((u11 (bvadd u10 u10)))
(let ((u12 (bvand u11 u11)))
(let ((u13 (bvadd u12 u12)))
(let ((u14 (bvand u13 u13)))
(let ((u15 (bvadd u14 u14)))
(let ((u16 (bvand u15 u15)))
(let ((u17 (bvadd u16 u16)))
(let ((u18 (bvand u17 u17)))
(let ((u19 (bvadd u18 u18)))
(bvand u19 u19))))))))))))))))))))
#b00000000))
(check-sat)
