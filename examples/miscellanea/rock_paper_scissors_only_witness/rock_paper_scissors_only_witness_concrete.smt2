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
(declare-const v_20 FFp)
(declare-const v_2 FFp)
(declare-const v_3 FFp)
(declare-const v_4 FFp)
(declare-const v_5 FFp)
(declare-const v_6 FFp)
(declare-const v_7 FFp)
(declare-const v_8 FFp)
(declare-const v_9 FFp)
(declare-const v_10 FFp)
(declare-const v_11 FFp)
(declare-const v_12 FFp)
(declare-const v_13 FFp)
(declare-const v_14 FFp)
(declare-const v_15 FFp)
(declare-const v_16 FFp)
(declare-const v_17 FFp)
(declare-const v_18 FFp)
(declare-const v_19 FFp)

(define-fun @RockPaperScissors_0 ((v_0 FFp) (v_1 FFp) (v_19 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp)) Bool
  (and 
    (and 
      (= v_2 (ite  (= v_1 v_0) 1 0))
      (ite 
        (= v_2 1)
        (and 
          true
          (= v_18 2)
        )
        (and 
          (and 
            (= v_3 (ite  (= 0 v_0) 1 0))
            (and 
              (= v_4 (ite  (= 2 v_1) 1 0))
              (and 
                (and 
                  (= v_5 (ite  (or  (= v_3 0) (= v_4 0) ) 0 1))
                  (ff.range v_5 0 1)
                )
                (and 
                  (ite 
                    (= v_5 1)
                    (and 
                      (and 
                        true
                        (= v_16 0)
                      )
                      (= v_17 0)
                    )
                    (and 
                      (and 
                        (and 
                          (= v_6 (ite  (= 1 v_0) 1 0))
                          (and 
                            (= v_7 (ite  (= 0 v_1) 1 0))
                            (and 
                              (and 
                                (= v_8 (ite  (or  (= v_6 0) (= v_7 0) ) 0 1))
                                (ff.range v_8 0 1)
                              )
                              (and 
                                (ite 
                                  (= v_8 1)
                                  (and 
                                    (and 
                                      true
                                      (= v_14 0)
                                    )
                                    (= v_15 0)
                                  )
                                  (and 
                                    (and 
                                      (and 
                                        (= v_9 (ite  (= 2 v_0) 1 0))
                                        (and 
                                          (= v_10 (ite  (= 1 v_1) 1 0))
                                          (and 
                                            (and 
                                              (= v_11 (ite  (or  (= v_9 0) (= v_10 0) ) 0 1))
                                              (ff.range v_11 0 1)
                                            )
                                            (and 
                                              (ite 
                                                (= v_11 1)
                                                (and 
                                                  (and 
                                                    true
                                                    (= v_12 0)
                                                  )
                                                  (= v_13 0)
                                                )
                                                (and 
                                                  (and 
                                                    true
                                                    (= v_12 1)
                                                  )
                                                  (= v_13 1)
                                                )
                                              )
                                              true
                                            )
                                          )
                                        )
                                      )
                                      (= v_14 v_12)
                                    )
                                    (= v_15 v_13)
                                  )
                                )
                                true
                              )
                            )
                          )
                        )
                        (= v_16 v_14)
                      )
                      (= v_17 v_15)
                    )
                  )
                  true
                )
              )
            )
          )
          (= v_18 v_17)
        )
      )
    )
    (= v_19 v_18)
  )
)


(define-fun main ((v_0 FFp) (v_1 FFp) (v_20 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp)) Bool
  (and 
    (@RockPaperScissors_0 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19)
    (= v_20 v_2)
  )
)


(assert 
  (main v_0 v_1 v_20 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19)
)
