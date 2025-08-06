(declare-fun fwd ((_ BitVec 32)) (_ BitVec 10))
(declare-fun fwd$ ((_ BitVec 32)) (_ BitVec 10))

(assert (forall ((dst (_ BitVec 32))) 
    (= (fwd dst) (fwd$ dst))))

(declare-const dst (_ BitVec 32))
(declare-const port$s (_ BitVec 9))
(declare-const port$t (_ BitVec 9))

(declare-const act (_ BitVec 1))
(assert (= act ((_ extract 0 0) (fwd dst))))
(declare-const data (_ BitVec 9))
(assert (= data ((_ extract 9 1) (fwd dst))))

(declare-const act$ (_ BitVec 1))
(assert (= act$ ((_ extract 0 0) (fwd$ dst))))
(declare-const data$ (_ BitVec 9))
(assert (= data$ ((_ extract 9 1) (fwd$ dst))))

(assert (=> (= act #b0) (= port$s (_ bv511 9))))
(assert (=> (= act #b1) (= port$s data)))

(assert (=> (= act$ #b0) (= port$t (_ bv511 9))))
(assert (=> (= act$ #b1) (= port$t data$)))
(assert (distinct port$s port$t))

(check-sat)
(get-model)