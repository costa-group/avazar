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
(declare-const v_48 FFp)
(declare-const v_1 FFp)
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
(declare-const v_30 FFp)
(declare-const v_31 FFp)
(declare-const v_32 FFp)
(declare-const v_33 FFp)
(declare-const v_34 FFp)
(declare-const v_35 FFp)
(declare-const v_36 FFp)
(declare-const v_37 FFp)
(declare-const v_38 FFp)
(declare-const v_39 FFp)
(declare-const v_40 FFp)
(declare-const v_41 FFp)
(declare-const v_42 FFp)
(declare-const v_43 FFp)
(declare-const v_44 FFp)
(declare-const v_45 FFp)
(declare-const v_46 FFp)
(declare-const v_47 FFp)

(define-fun @MultiMux2_0 ((v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_18 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp)) Bool
  (and 
    (and 
      (= v_6 (ff.mul v_5 v_4))
      (and 
        (= v_7 (ff.sub v_3 v_2))
        (and 
          (= v_8 (ff.sub v_7 v_1))
          (and 
            (= v_9 (ff.add v_8 v_0))
            (and 
              (= v_10 (ff.mul v_9 v_6))
              (and 
                (= v_11 (ff.sub v_2 v_0))
                (and 
                  (= v_12 (ff.mul v_11 v_5))
                  (and 
                    (= v_13 (ff.sub v_1 v_0))
                    (and 
                      (= v_14 (ff.mul v_13 v_4))
                      (and 
                        (= v_15 (ff.add v_10 v_12))
                        (and 
                          (= v_16 (ff.add v_15 v_14))
                          (and 
                            (= v_17 (ff.add v_16 v_0))
                            true
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
    (= v_18 v_17)
  )
)


(define-fun @Mux2_1 ((v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_19 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp)) Bool
  (and 
    (and 
      (and 
        true
        (and 
          true
          (and 
            true
            true
          )
        )
      )
      (and 
        (and 
          true
          (and 
            (and 
              (@MultiMux2_0 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18)
              true
            )
            true
          )
        )
        true
      )
    )
    (= v_19 v_6)
  )
)


(define-fun @Num2Bits_2 ((v_0 FFp) (v_33 FFp) (v_34 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_31 FFp) (v_32 FFp)) Bool
  (and 
    (and 
      (and 
        (and 
          (and 
            (and 
              (and 
                (and 
                  (and 
                    (and 
                      (= v_0 (ff.add (ff.add (ff.add (ff.mul v_2 1) (ff.mul v_3 2)) (ff.mul v_4 4)) (ff.mul v_5 8)))
                      (= (ff.mul v_2 (ff.sub 1 v_2)) 0)
                    )
                    (= (ff.mul v_3 (ff.sub 1 v_3)) 0)
                  )
                  (= (ff.mul v_4 (ff.sub 1 v_4)) 0)
                )
                (= (ff.mul v_5 (ff.sub 1 v_5)) 0)
              )
              (= v_1 (ff.add (ff.add (ff.add (ff.mul (ff.mul v_2 1) 1) (ff.mul (ff.mul v_3 2) 2)) (ff.mul (ff.mul v_4 4) 4)) (ff.mul (ff.mul v_5 8) 8)))
            )
            (and 
              (and 
                (and 
                  (and 
                    (and 
                      (and 
                        (and 
                          (= v_1 (ff.add (ff.add (ff.add (ff.mul v_7 1) (ff.mul v_8 2)) (ff.mul v_9 4)) (ff.mul v_10 8)))
                          (= (ff.mul v_7 (ff.sub 1 v_7)) 0)
                        )
                        (= (ff.mul v_8 (ff.sub 1 v_8)) 0)
                      )
                      (= (ff.mul v_9 (ff.sub 1 v_9)) 0)
                    )
                    (= (ff.mul v_10 (ff.sub 1 v_10)) 0)
                  )
                  (and 
                    (= 1 (ff.mul 1 1))
                    (and 
                      (= v_6 (ff.mul v_11 1))
                      (= (ff.mul v_11 (ff.sub 1 v_11)) 0)
                    )
                  )
                )
                (= v_11 (ff.mul v_7 1))
              )
              (and 
                (= v_15 (ff.mul v_6 1))
                (and 
                  (= v_16 (ff.add 0 v_15))
                  true
                )
              )
            )
          )
          (and 
            (and 
              (and 
                (and 
                  (and 
                    (and 
                      (= v_0 (ff.add (ff.add (ff.add (ff.mul v_18 1) (ff.mul v_19 2)) (ff.mul v_20 4)) (ff.mul v_21 8)))
                      (= (ff.mul v_18 (ff.sub 1 v_18)) 0)
                    )
                    (= (ff.mul v_19 (ff.sub 1 v_19)) 0)
                  )
                  (= (ff.mul v_20 (ff.sub 1 v_20)) 0)
                )
                (= (ff.mul v_21 (ff.sub 1 v_21)) 0)
              )
              (= v_17 (ff.add (ff.add (ff.mul (ff.mul v_19 1) 1) (ff.mul (ff.mul v_20 2) 2)) (ff.mul (ff.mul v_21 4) 4)))
            )
            (and 
              (and 
                (and 
                  (and 
                    (and 
                      (and 
                        (and 
                          (= v_17 (ff.add (ff.add (ff.add (ff.mul v_23 1) (ff.mul v_24 2)) (ff.mul v_25 4)) (ff.mul v_26 8)))
                          (= (ff.mul v_23 (ff.sub 1 v_23)) 0)
                        )
                        (= (ff.mul v_24 (ff.sub 1 v_24)) 0)
                      )
                      (= (ff.mul v_25 (ff.sub 1 v_25)) 0)
                    )
                    (= (ff.mul v_26 (ff.sub 1 v_26)) 0)
                  )
                  (and 
                    (= 1 (ff.mul 1 1))
                    (and 
                      (= v_22 (ff.mul v_27 1))
                      (= (ff.mul v_27 (ff.sub 1 v_27)) 0)
                    )
                  )
                )
                (= v_27 (ff.mul v_23 1))
              )
              (and 
                (= v_31 (ff.mul v_22 1))
                (and 
                  (= v_32 (ff.add v_16 v_31))
                  true
                )
              )
            )
          )
        )
        true
      )
      (= v_33 v_6)
    )
    (= v_34 v_22)
  )
)


(define-fun @Constants_3 ((v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp)) Bool
  (and 
    (and 
      (and 
        (and 
          true
          (= v_0 4)
        )
        (= v_1 3)
      )
      (= v_2 9)
    )
    (= v_3 5)
  )
)


(define-fun @Main_4 ((v_0 FFp) (v_47 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp)) Bool
  (and 
    (and 
      (@Constants_3 v_1 v_2 v_3 v_4)
      (and 
        (and 
          (@Num2Bits_2 v_0 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32)
          true
        )
        (and 
          (and 
            true
            true
          )
          (and 
            (and 
              true
              (and 
                true
                (and 
                  true
                  (and 
                    (and 
                      (@Mux2_1 v_1 v_2 v_3 v_4 v_5 v_6 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46)
                      true
                    )
                    true
                  )
                )
              )
            )
            true
          )
        )
      )
    )
    (= v_47 v_33)
  )
)


(define-fun main ((v_0 FFp) (v_48 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp) (v_47 FFp)) Bool
  (and 
    (@Main_4 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47)
    (= v_48 v_1)
  )
)


(assert 
  (main v_0 v_48 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47)
)
