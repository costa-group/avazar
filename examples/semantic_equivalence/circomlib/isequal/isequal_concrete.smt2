(set-logic QF_FF)

; (define-sort FFp () (_ FiniteField 11))
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
(declare-const v_1 FFp)
(declare-const v_11 FFp)
(declare-const v_2 FFp)
(declare-const v_3 FFp)
(declare-const v_4 FFp)
(declare-const v_5 FFp)
(declare-const v_6 FFp)
(declare-const v_7 FFp)
(declare-const v_8 FFp)
(declare-const v_9 FFp)
(declare-const v_10 FFp)

(define-fun @IsZero_0 ((v_0 FFp) (v_7 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp)) Bool
  (and 
    (and 
      (= v_1 (ite  (= 0 v_0) 0 1))
      (and 
        (ite 
          (= v_1 1)
          (and 
            (and 
              (= (ff.mul v_2 v_0) 1)
              true
            )
            (= v_3 v_2)
          )
          (and 
            true
            (= v_3 0)
          )
        )
        (and 
          (= v_4 (ff.neg v_0))
          (and 
            (= v_5 (ff.mul v_4 v_3))
            (and 
              (= v_6 (ff.add v_5 1))
              true
            )
          )
        )
      )
    )
    (= v_7 v_6)
  )
)


(define-fun @IsEqual_1 ((v_0 FFp) (v_1 FFp) (v_10 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp)) Bool
  (and 
    (and 
      (= v_2 (ff.sub v_1 v_0))
      (and 
        (and 
          (@IsZero_0 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9)
          true
        )
        true
      )
    )
    (= v_10 v_3)
  )
)


(define-fun main ((v_0 FFp) (v_1 FFp) (v_11 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp)) Bool
  (and 
    (@IsEqual_1 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10)
    (= v_11 v_2)
  )
)


(assert 
  (main v_0 v_1 v_11 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10)
)
