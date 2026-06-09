(set-logic QF_FF)

; (define-sort FFp () (_ FiniteField 11))
(define-sort FFp () Int)
(declare-fun ff.add (FFp FFp) FFp)
(declare-fun ff.mul (FFp FFp) FFp)
(declare-fun ff.sub (FFp FFp) FFp)
(declare-fun ff.neg (FFp) FFp)

(declare-fun ff.lt (FFp FFp) Bool)
(declare-fun ff.gt (FFp FFp) Bool)
(declare-fun ff.le (FFp FFp) Bool)
(declare-fun ff.ge (FFp FFp) Bool)

(declare-const v_0 FFp)
(declare-const v_1 FFp)
(declare-const v_30 FFp)
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
(declare-const v_20 FFp)
(declare-const v_21 FFp)
(declare-const v_22 FFp)
(declare-const v_23 FFp)
(declare-const v_24 FFp)
(declare-const v_25 FFp)
(declare-const v_26 FFp)
(declare-const v_27 FFp)
(declare-const v_28 FFp)
(declare-const v_29 FFp)

(define-fun @RockPaperScissors_0 ((v_0 FFp) (v_1 FFp) (v_29 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp)) Bool
  (and 
    (and 
      (= v_2 (ite  (= 2 v_0) 1 0))
      (and 
        (= v_3 (ite  (= 3 v_0) 1 0))
        (and 
          (and 
            (= v_4 (ite  (and  (= v_2 0) (= v_3 0) ) 0 1))
            (or (= v_4 0) (= v_4 1))
          )
          (and 
            (= v_5 (ite  (= 5 v_0) 1 0))
            (and 
              (and 
                (= v_6 (ite  (and  (= v_4 0) (= v_5 0) ) 0 1))
            (or (= v_6 0) (= v_6 1))
              )
              (and 
                (= v_7 (ite  (= 2 v_1) 1 0))
                (and 
                  (= v_8 (ite  (= 3 v_1) 1 0))
                  (and 
                    (and 
                      (= v_9 (ite  (and  (= v_7 0) (= v_8 0) ) 0 1))
            (or (= v_9 0) (= v_9 1))
                    )
                    (and 
                      (= v_10 (ite  (= 5 v_1) 1 0))
                      (and 
                        (and 
                          (= v_11 (ite  (and  (= v_9 0) (= v_10 0) ) 0 1))
            (or (= v_11 0) (= v_11 1))
                        )
                        (and 
                          (= v_12 (ite  (= v_1 v_0) 1 0))
                          (ite 
                            (= v_12 1)
                            (and 
                              true
                              (= v_28 0)
                            )
                            (and 
                              (and 
                                (= v_13 (ite  (= 2 v_0) 1 0))
                                (and 
                                  (= v_14 (ite  (= 5 v_1) 1 0))
                                  (and 
                                    (and 
                                      (= v_15 (ite  (or  (= v_13 0) (= v_14 0) ) 0 1))
            (or (= v_15 0) (= v_15 1))
                                    )
                                    (and 
                                      (ite 
                                        (= v_15 1)
                                        (and 
                                          (and 
                                            true
                                            (= v_26 1)
                                          )
                                          (= v_27 1)
                                        )
                                        (and 
                                          (and 
                                            (and 
                                              (= v_16 (ite  (= 3 v_0) 1 0))
                                              (and 
                                                (= v_17 (ite  (= 2 v_1) 1 0))
                                                (and 
                                                  (and 
                                                    (= v_18 (ite  (or  (= v_16 0) (= v_17 0) ) 0 1))
            (or (= v_18 0) (= v_18 1))
                                                  )
                                                  (and 
                                                    (ite 
                                                      (= v_18 1)
                                                      (and 
                                                        (and 
                                                          true
                                                          (= v_24 1)
                                                        )
                                                        (= v_25 1)
                                                      )
                                                      (and 
                                                        (and 
                                                          (and 
                                                            (= v_19 (ite  (= 5 v_0) 1 0))
                                                            (and 
                                                              (= v_20 (ite  (= 3 v_1) 1 0))
                                                              (and 
                                                                (and 
                                                                  (= v_21 (ite  (or  (= v_19 0) (= v_20 0) ) 0 1))
            (or (= v_21 0) (= v_21 1))
                                                                )
                                                                (and 
                                                                  (ite 
                                                                    (= v_21 1)
                                                                    (and 
                                                                      (and 
                                                                        true
                                                                        (= v_22 1)
                                                                      )
                                                                      (= v_23 1)
                                                                    )
                                                                    (and 
                                                                      (and 
                                                                        true
                                                                        (= v_22 2)
                                                                      )
                                                                      (= v_23 2)
                                                                    )
                                                                  )
                                                                  true
                                                                )
                                                              )
                                                            )
                                                          )
                                                          (= v_24 v_22)
                                                        )
                                                        (= v_25 v_23)
                                                      )
                                                    )
                                                    true
                                                  )
                                                )
                                              )
                                            )
                                            (= v_26 v_24)
                                          )
                                          (= v_27 v_25)
                                        )
                                      )
                                      true
                                    )
                                  )
                                )
                              )
                              (= v_28 v_27)
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (= v_29 v_28)
  )
)


(define-fun main ((v_0 FFp) (v_1 FFp) (v_30 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp)) Bool
  (and 
    (@RockPaperScissors_0 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29)
    (= v_30 v_2)
  )
)


(assert 
  (main v_0 v_1 v_30 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29)
)
