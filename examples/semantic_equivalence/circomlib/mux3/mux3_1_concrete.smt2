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
(declare-const v_88 FFp)
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
(declare-const v_48 FFp)
(declare-const v_49 FFp)
(declare-const v_50 FFp)
(declare-const v_51 FFp)
(declare-const v_52 FFp)
(declare-const v_53 FFp)
(declare-const v_54 FFp)
(declare-const v_55 FFp)
(declare-const v_56 FFp)
(declare-const v_57 FFp)
(declare-const v_58 FFp)
(declare-const v_59 FFp)
(declare-const v_60 FFp)
(declare-const v_61 FFp)
(declare-const v_62 FFp)
(declare-const v_63 FFp)
(declare-const v_64 FFp)
(declare-const v_65 FFp)
(declare-const v_66 FFp)
(declare-const v_67 FFp)
(declare-const v_68 FFp)
(declare-const v_69 FFp)
(declare-const v_70 FFp)
(declare-const v_71 FFp)
(declare-const v_72 FFp)
(declare-const v_73 FFp)
(declare-const v_74 FFp)
(declare-const v_75 FFp)
(declare-const v_76 FFp)
(declare-const v_77 FFp)
(declare-const v_78 FFp)
(declare-const v_79 FFp)
(declare-const v_80 FFp)
(declare-const v_81 FFp)
(declare-const v_82 FFp)
(declare-const v_83 FFp)
(declare-const v_84 FFp)
(declare-const v_85 FFp)
(declare-const v_86 FFp)
(declare-const v_87 FFp)

(define-fun @MultiMux3_0 ((v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_45 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp)) Bool
  (and 
    (and 
      (= v_11 (ff.mul v_9 v_8))
      (and 
        (= v_12 (ff.sub v_7 v_6))
        (and 
          (= v_13 (ff.sub v_12 v_5))
          (and 
            (= v_14 (ff.add v_13 v_4))
            (and 
              (= v_15 (ff.sub v_14 v_3))
              (and 
                (= v_16 (ff.add v_15 v_2))
                (and 
                  (= v_17 (ff.add v_16 v_1))
                  (and 
                    (= v_18 (ff.sub v_17 v_0))
                    (and 
                      (= v_19 (ff.mul v_18 v_11))
                      (and 
                        (= v_20 (ff.sub v_6 v_4))
                        (and 
                          (= v_21 (ff.sub v_20 v_2))
                          (and 
                            (= v_22 (ff.add v_21 v_0))
                            (and 
                              (= v_23 (ff.mul v_22 v_9))
                              (and 
                                (= v_24 (ff.sub v_5 v_4))
                                (and 
                                  (= v_25 (ff.sub v_24 v_1))
                                  (and 
                                    (= v_26 (ff.add v_25 v_0))
                                    (and 
                                      (= v_27 (ff.mul v_26 v_8))
                                      (and 
                                        (= v_28 (ff.sub v_4 v_0))
                                        (and 
                                          (= v_29 (ff.sub v_3 v_2))
                                          (and 
                                            (= v_30 (ff.sub v_29 v_1))
                                            (and 
                                              (= v_31 (ff.add v_30 v_0))
                                              (and 
                                                (= v_32 (ff.mul v_31 v_11))
                                                (and 
                                                  (= v_33 (ff.sub v_2 v_0))
                                                  (and 
                                                    (= v_34 (ff.mul v_33 v_9))
                                                    (and 
                                                      (= v_35 (ff.sub v_1 v_0))
                                                      (and 
                                                        (= v_36 (ff.mul v_35 v_8))
                                                        (and 
                                                          (= v_37 (ff.add v_19 v_23))
                                                          (and 
                                                            (= v_38 (ff.add v_37 v_27))
                                                            (and 
                                                              (= v_39 (ff.add v_38 v_28))
                                                              (and 
                                                                (= v_40 (ff.mul v_39 v_10))
                                                                (and 
                                                                  (= v_41 (ff.add v_32 v_34))
                                                                  (and 
                                                                    (= v_42 (ff.add v_41 v_36))
                                                                    (and 
                                                                      (= v_43 (ff.add v_42 v_0))
                                                                      (and 
                                                                        (= v_44 (ff.add v_40 v_43))
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
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (= v_45 v_44)
  )
)


(define-fun @Mux3_1 ((v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_46 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp)) Bool
  (and 
    (and 
      (and 
        true
        (and 
          true
          (and 
            true
            (and 
              true
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
            )
          )
        )
      )
      (and 
        (and 
          true
          (and 
            true
            (and 
              (and 
                (@MultiMux3_0 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45)
                true
              )
              true
            )
          )
        )
        true
      )
    )
    (= v_46 v_11)
  )
)


(define-fun @Num2Bits_2 ((v_0 FFp) (v_49 FFp) (v_50 FFp) (v_51 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_47 FFp) (v_48 FFp)) Bool
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
              (and 
                (and 
                  (and 
                    (and 
                      (and 
                        (and 
                          (= v_0 (ff.add (ff.add (ff.add (ff.mul v_34 1) (ff.mul v_35 2)) (ff.mul v_36 4)) (ff.mul v_37 8)))
                          (= (ff.mul v_34 (ff.sub 1 v_34)) 0)
                        )
                        (= (ff.mul v_35 (ff.sub 1 v_35)) 0)
                      )
                      (= (ff.mul v_36 (ff.sub 1 v_36)) 0)
                    )
                    (= (ff.mul v_37 (ff.sub 1 v_37)) 0)
                  )
                  (= v_33 (ff.add (ff.mul (ff.mul v_36 1) 1) (ff.mul (ff.mul v_37 2) 2)))
                )
                (and 
                  (and 
                    (and 
                      (and 
                        (and 
                          (and 
                            (and 
                              (= v_33 (ff.add (ff.add (ff.add (ff.mul v_39 1) (ff.mul v_40 2)) (ff.mul v_41 4)) (ff.mul v_42 8)))
                              (= (ff.mul v_39 (ff.sub 1 v_39)) 0)
                            )
                            (= (ff.mul v_40 (ff.sub 1 v_40)) 0)
                          )
                          (= (ff.mul v_41 (ff.sub 1 v_41)) 0)
                        )
                        (= (ff.mul v_42 (ff.sub 1 v_42)) 0)
                      )
                      (and 
                        (= 1 (ff.mul 1 1))
                        (and 
                          (= v_38 (ff.mul v_43 1))
                          (= (ff.mul v_43 (ff.sub 1 v_43)) 0)
                        )
                      )
                    )
                    (= v_43 (ff.mul v_39 1))
                  )
                  (and 
                    (= v_47 (ff.mul v_38 1))
                    (and 
                      (= v_48 (ff.add v_32 v_47))
                      true
                    )
                  )
                )
              )
            )
          )
          true
        )
        (= v_49 v_6)
      )
      (= v_50 v_22)
    )
    (= v_51 v_38)
  )
)


(define-fun @Constants_3 ((v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp)) Bool
  (and 
    (and 
      (and 
        (and 
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
          (= v_4 1)
        )
        (= v_5 8)
      )
      (= v_6 9)
    )
    (= v_7 4)
  )
)


(define-fun @Main_4 ((v_0 FFp) (v_87 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp) (v_47 FFp) (v_48 FFp) (v_49 FFp) (v_50 FFp) (v_51 FFp) (v_52 FFp) (v_53 FFp) (v_54 FFp) (v_55 FFp) (v_56 FFp) (v_57 FFp) (v_58 FFp) (v_59 FFp) (v_60 FFp) (v_61 FFp) (v_62 FFp) (v_63 FFp) (v_64 FFp) (v_65 FFp) (v_66 FFp) (v_67 FFp) (v_68 FFp) (v_69 FFp) (v_70 FFp) (v_71 FFp) (v_72 FFp) (v_73 FFp) (v_74 FFp) (v_75 FFp) (v_76 FFp) (v_77 FFp) (v_78 FFp) (v_79 FFp) (v_80 FFp) (v_81 FFp) (v_82 FFp) (v_83 FFp) (v_84 FFp) (v_85 FFp) (v_86 FFp)) Bool
  (and 
    (and 
      (@Constants_3 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8)
      (and 
        (and 
          (@Num2Bits_2 v_0 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50)
          true
        )
        (and 
          (and 
            true
            (and 
              true
              true
            )
          )
          (and 
            (and 
              true
              (and 
                true
                (and 
                  true
                  (and 
                    true
                    (and 
                      true
                      (and 
                        true
                        (and 
                          true
                          (and 
                            (and 
                              (@Mux3_1 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_51 v_52 v_53 v_54 v_55 v_56 v_57 v_58 v_59 v_60 v_61 v_62 v_63 v_64 v_65 v_66 v_67 v_68 v_69 v_70 v_71 v_72 v_73 v_74 v_75 v_76 v_77 v_78 v_79 v_80 v_81 v_82 v_83 v_84 v_85 v_86)
                              true
                            )
                            true
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
            true
          )
        )
      )
    )
    (= v_87 v_51)
  )
)


(define-fun main ((v_0 FFp) (v_88 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp) (v_47 FFp) (v_48 FFp) (v_49 FFp) (v_50 FFp) (v_51 FFp) (v_52 FFp) (v_53 FFp) (v_54 FFp) (v_55 FFp) (v_56 FFp) (v_57 FFp) (v_58 FFp) (v_59 FFp) (v_60 FFp) (v_61 FFp) (v_62 FFp) (v_63 FFp) (v_64 FFp) (v_65 FFp) (v_66 FFp) (v_67 FFp) (v_68 FFp) (v_69 FFp) (v_70 FFp) (v_71 FFp) (v_72 FFp) (v_73 FFp) (v_74 FFp) (v_75 FFp) (v_76 FFp) (v_77 FFp) (v_78 FFp) (v_79 FFp) (v_80 FFp) (v_81 FFp) (v_82 FFp) (v_83 FFp) (v_84 FFp) (v_85 FFp) (v_86 FFp) (v_87 FFp)) Bool
  (and 
    (@Main_4 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50 v_51 v_52 v_53 v_54 v_55 v_56 v_57 v_58 v_59 v_60 v_61 v_62 v_63 v_64 v_65 v_66 v_67 v_68 v_69 v_70 v_71 v_72 v_73 v_74 v_75 v_76 v_77 v_78 v_79 v_80 v_81 v_82 v_83 v_84 v_85 v_86 v_87)
    (= v_88 v_1)
  )
)


(assert 
  (main v_0 v_88 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50 v_51 v_52 v_53 v_54 v_55 v_56 v_57 v_58 v_59 v_60 v_61 v_62 v_63 v_64 v_65 v_66 v_67 v_68 v_69 v_70 v_71 v_72 v_73 v_74 v_75 v_76 v_77 v_78 v_79 v_80 v_81 v_82 v_83 v_84 v_85 v_86 v_87)
)
