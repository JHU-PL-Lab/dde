(set-logic HORN)
(set-option :fp.xform.inline_linear false)
(set-option :fp.xform.inline_eager false)
(declare-fun P0 (Bool) Bool)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int) Bool)
;; (assert (forall ((r1 Int) (r2 Int) (r Bool)) 
;; (=> (and (P1 r1) (and (P2 r2) (= r (= r1 r2))))(P0 r))))
(assert (forall ((r1 Int) (r2 Int)) 
  (=> (and (P1 r1) (P2 r2)) (P0 (= r1 r2)))))
(assert (P1 1))
(assert (P2 2))
(assert (=> (P0 false) false))
;(assert (=> (P0 true) false))
;(assert (P0 true)) ; seems same as previous but need the implies false to give it a negation to search from.
(check-sat)
;(get-model)
