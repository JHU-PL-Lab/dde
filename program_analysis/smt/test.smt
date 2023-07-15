(set-logic HORN)
(set-option :fp.xform.inline_linear false)
(set-option :fp.xform.inline_eager false)
(declare-fun P0 (Int) Bool)
(declare-fun P45 (Int) Bool)
(declare-fun P31 (Bool) Bool)
(declare-fun P18 (Bool) Bool)
(declare-fun P3 (Bool) Bool)
(declare-fun P48 (Int) Bool)
(declare-fun P15 (Int) Bool)
(declare-fun P40 (Int) Bool)
(declare-fun P43 (Int) Bool)
(declare-fun P4 (Int) Bool)
(declare-fun P10 (Int) Bool)
(declare-fun P2 (Int) Bool)
(declare-fun P44 (Bool) Bool)
(declare-fun P9 (Int) Bool)
(declare-fun P39 (Int) Bool)
(declare-fun P41 (Int) Bool)
(declare-fun P56 (Int) Bool)
(declare-fun P22 (Int) Bool)
(declare-fun P24 (Int) Bool)
(declare-fun P13 (Int) Bool)
(declare-fun P23 (Int) Bool)
(declare-fun P37 (Int) Bool)
(declare-fun P36 (Int) Bool)
(declare-fun P14 (Int) Bool)
(declare-fun P12 (Int) Bool)
(declare-fun P50 (Int) Bool)
(declare-fun P49 (Int) Bool)
(declare-fun P52 (Int) Bool)
(declare-fun P54 (Int) Bool)
(declare-fun P8 (Int) Bool)
(declare-fun P11 (Int) Bool)
(declare-fun P5 (Int) Bool)
(declare-fun P35 (Int) Bool)
(declare-fun P17 (Int) Bool)
(declare-fun P46 (Bool) Bool)
(declare-fun P26 (Int) Bool)
(declare-fun P28 (Int) Bool)
(declare-fun P30 (Int) Bool)
(declare-fun P53 (Int) Bool)
(declare-fun P19 (Int) Bool)
(declare-fun P33 (Bool) Bool)
(declare-fun P6 (Bool) Bool)
(declare-fun P20 (Bool) Bool)
(declare-fun P27 (Int) Bool)
(declare-fun P32 (Int) Bool)
(declare-fun P58 (Int) Bool)
(declare-fun P57 (Int) Bool)
(assert (forall ((r Int)) (=> (P0 r) (>= r 3))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P48 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P45 r))))
(assert (forall ((c0 Bool) (c1 Bool))
  (=> (and (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P15 1))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P43 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P40 r))))
(assert (forall ((r Int) (c0 Bool)) (=> (and (P10 r) (P3 c0) (= c0 false) true) (P4 r))))
(assert (forall ((r Int)) (=> (and (P2 r) true) (P0 r))))
(assert (forall ((c0 Bool) (c1 Bool) (c2 Bool) (c3 Bool))
  (=> (and (P3 c3)
           (= c3 false)
           (P18 c2)
           (= c2 false)
           (P31 c1)
           (= c1 false)
           (P44 c0)
           (= c0 true)
           true)
      (P10 0))))
(assert (forall ((c0 Bool)) (=> (and (P3 c0) (= c0 false) true) (P9 10))))
(assert (forall ((c0 Bool) (c1 Bool) (c2 Bool) (c3 Bool))
  (=> (and (P3 c3)
           (= c3 false)
           (P18 c2)
           (= c2 false)
           (P31 c1)
           (= c1 false)
           (P44 c0)
           (= c0 false)
           true)
      (P15 1))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P41 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P39 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P56 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P43 r))))
(assert (forall ((r Int) (c0 Bool))
  (=> (and (P24 r) (P3 c0) (= c0 false) true) (P22 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P23 r1)
           (P13 r2)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P24 (- r1 r2)))))
(assert (forall ((r Int) (c0 Bool))
  (=> (and (P15 r) (P3 c0) (= c0 false) true) (P13 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P36 r1)
           (P13 r2)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P37 (- r1 r2)))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool))
  (=> (and (P13 r1) (P12 r2) (P3 c0) (= c0 false) true) (P14 (+ r1 r2)))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P49 r1)
           (P13 r2)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P50 (- r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P54 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P52 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P8 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P23 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P9 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P8 r))))
(assert (forall ((r Int) (c0 Bool))
  (=> (and (P14 r) (P3 c0) (= c0 false) true) (P11 r))))
(assert (forall ((r Int)) (=> (and (P9 r) true) (P8 r))))
(assert (forall ((c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P10 0))))
(assert (forall ((r Int)) (=> (and (P8 r) true) (P5 r))))
(assert (forall ((r Int)) (=> (and (P11 r) true) (P2 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P37 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P35 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool))
  (=> (and (P36 r1) (P13 r2) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true)
      (P37 (- r1 r2)))))
(assert (forall ((r Int) (c0 Bool))
  (=> (and (P17 r) (P3 c0) (= c0 false) true) (P12 r))))
(assert (forall ((c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P9 10))))
(assert (forall ((c0 Bool)) (=> (and (P3 c0) (= c0 false) true) (P10 0))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P37 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P52 r))))
(assert (P9 10))
(assert (forall ((r Bool) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P46 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P44 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P28 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P26 r))))
(assert (forall ((c0 Bool)) (=> (and (P3 c0) (= c0 false) true) (P15 1))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool))
  (=> (and (P23 r1) (P13 r2) (P3 c0) (= c0 false) true) (P24 (- r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool) (c3 Bool))
  (=> (and (P10 r)
           (P3 c3)
           (= c3 false)
           (P18 c2)
           (= c2 false)
           (P31 c1)
           (= c1 false)
           (P44 c0)
           (= c0 true)
           true)
      (P4 r))))
(assert (forall ((c0 Bool) (c1 Bool))
  (=> (and (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P10 0))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool) (c3 Bool))
  (=> (and (P15 r)
           (P3 c3)
           (= c3 false)
           (P18 c2)
           (= c2 false)
           (P31 c1)
           (= c1 false)
           (P44 c0)
           (= c0 false)
           true)
      (P13 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P45 r1)
           (P4 r2)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P46 (= r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P22 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P36 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P39 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P30 r))))
(assert (forall ((c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P15 1))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P53 r1)
           (P13 r2)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P54 (- r1 r2)))))
(assert (forall ((r Int) (c0 Bool)) (=> (and (P8 r) (P3 c0) (= c0 false) true) (P23 r))))
(assert (forall ((r Int) (c0 Bool)) (=> (and (P9 r) (P3 c0) (= c0 false) true) (P8 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P13 r1)
           (P40 r2)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P41 (+ r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P52 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P49 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P10 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P4 r))))
(assert (forall ((r Int) (c0 Bool))
  (=> (and (P22 r) (P3 c0) (= c0 false) true) (P19 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P8 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P23 r))))
(assert (forall ((r Bool) (c0 Bool) (c1 Bool))
  (=> (and (P33 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P31 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P50 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P48 r))))
(assert (forall ((r Bool)) (=> (and (P6 r) true) (P3 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P10 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P4 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P15 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P13 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool))
  (=> (and (P19 r1) (P4 r2) (P3 c0) (= c0 false) true) (P20 (= r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P4 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P43 r))))
(assert (forall ((r Int) (c0 Bool))
  (=> (and (P26 r) (P3 c0) (= c0 false) true) (P17 r))))
(assert (forall ((r Int)) (=> (and (P10 r) true) (P4 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool))
  (=> (and (P13 r1) (P27 r2) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true)
      (P28 (+ r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P30 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P27 r))))
(assert (P10 0))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P37 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P48 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P15 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P13 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P24 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P22 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P24 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P22 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P22 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P36 r))))
(assert (forall ((c0 Bool) (c1 Bool))
  (=> (and (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P9 10))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool))
  (=> (and (P32 r1) (P4 r2) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true)
      (P33 (= r1 r2)))))
(assert (forall ((r1 Int) (r2 Int)) (=> (and (P5 r1) (P4 r2) true) (P6 (= r1 r2)))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool))
  (=> (and (P23 r1) (P13 r2) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true)
      (P24 (- r1 r2)))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool) (c3 Bool))
  (=> (and (P58 r)
           (P3 c3)
           (= c3 false)
           (P18 c2)
           (= c2 false)
           (P31 c1)
           (= c1 false)
           (P44 c0)
           (= c0 false)
           true)
      (P56 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool) (c2 Bool))
  (=> (and (P9 r)
           (P3 c2)
           (= c2 false)
           (P18 c1)
           (= c1 false)
           (P31 c0)
           (= c0 false)
           true)
      (P8 r))))
(assert (forall ((r Int) (c0 Bool) (c1 Bool))
  (=> (and (P35 r) (P3 c1) (= c1 false) (P18 c0) (= c0 false) true) (P32 r))))
(assert (forall ((r1 Int) (r2 Int) (c0 Bool) (c1 Bool) (c2 Bool) (c3 Bool))
  (=> (and (P13 r1)
           (P57 r2)
           (P3 c3)
           (= c3 false)
           (P18 c2)
           (= c2 false)
           (P31 c1)
           (= c1 false)
           (P44 c0)
           (= c0 false)
           true)
      (P58 (+ r1 r2)))))
(assert (forall ((r Bool) (c0 Bool))
  (=> (and (P20 r) (P3 c0) (= c0 false) true) (P18 r))))
(check-sat)
(get-model)