(set-logic QF_FF)

; (define-sort FFp () (_ FiniteField 18446744069414584321))
(define-sort FFp () Int)
(declare-fun ff.add (FFp FFp) FFp)
(declare-fun ff.mul (FFp FFp) FFp)
(declare-fun ff.sub (FFp FFp) FFp)
(declare-fun ff.neg (FFp) FFp)
(declare-fun ff.range (FFp FFp FFp) Bool)
(declare-fun ff.lt (FFp FFp) Bool)
(declare-fun ff.gt (FFp FFp) Bool)
(declare-fun ff.le (FFp FFp) Bool)
(declare-fun ff.ge (FFp FFp) Bool)

(declare-const v_0 FFp)
(declare-const v_3 FFp)
(declare-const v_1 FFp)

(define-fun main ((v_0 FFp) (v_3 FFp) (v_1 FFp)) Bool
  (and 
    (and 
      (= v_1 (ff.mul 2 v_0))
      true
    )
    (= v_3 v_1)
  )
)


(assert 
  (main v_0 v_3 v_1)
)
