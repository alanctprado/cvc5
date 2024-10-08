; COMMAND-LINE: -q
; EXPECT: unsat
;; Unary OR is not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-sort e 0)
(declare-sort p 0)
(declare-fun t (p) Int)
(declare-fun o (Int) p)
(assert (forall ((x Int)) (! (= 0 x) :pattern ((o x)))))
(declare-datatypes ((s 0)) (((s_1 (x e) (e2 e) (c e) (c_ p)))))
(declare-datatypes ((us 0)) (((re (_s s)))))
(declare-datatypes ((_s2 0)) (((s_ (e3 (Array Int us))))))
(declare-datatypes ((us_ 0)) (((us4 (us3 _s2)))))
(declare-datatypes ((s_2 0)) (((us2 (re2 Bool)))))
(declare-datatypes ((u 0)) (((us5 (_s3 s_2)))))
(declare-fun e1 (us_ Int) (Array Int u))
(declare-const r e)
(assert (forall ((p1 us_)) (forall ((a Int)) (! (not (ite (forall ((i Int)) (= (t (c_ (_s (select (e3 (us3 p1)) i)))) (t (c_ (_s (re (s_1 r r r (o 0)))))))) true false)) :pattern ((e1 p1 0))))))
(assert (exists ((f _s2)) (or (forall ((n Int)) (or (forall ((j Int)) (= true (re2 (_s3 (select (e1 (us4 f) 0) 0))))))))))
(check-sat)
