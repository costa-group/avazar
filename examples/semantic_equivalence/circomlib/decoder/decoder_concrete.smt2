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

(define-fun @Decoder_0 ((v_0 FFp) (v_121 FFp) (v_122 FFp) (v_123 FFp) (v_124 FFp) (v_125 FFp) (v_126 FFp) (v_127 FFp) (v_128 FFp) (v_129 FFp) (v_130 FFp) (v_131 FFp) (v_0 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_12 FFp) (v_13 FFp) (v_24 FFp) (v_25 FFp) (v_36 FFp) (v_37 FFp) (v_48 FFp) (v_49 FFp) (v_60 FFp) (v_61 FFp) (v_72 FFp) (v_73 FFp) (v_84 FFp) (v_85 FFp) (v_96 FFp) (v_97 FFp) (v_108 FFp) (v_109 FFp) (v_120 FFp)) Bool
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
                        (and 
                          (and 
                            (and 
                              (= v_1 (ite  (= 0 v_0) 1 0))
                              (and 
                                (ite 
                                  (= v_1 1)
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
                                                      true
                                                      (= v_0 1)
                                                    )
                                                    (= v_1 0)
                                                  )
                                                  (= v_2 0)
                                                )
                                                (= v_3 0)
                                              )
                                              (= v_4 0)
                                            )
                                            (= v_5 0)
                                          )
                                          (= v_6 0)
                                        )
                                        (= v_7 0)
                                      )
                                      (= v_8 0)
                                    )
                                    (= v_9 0)
                                  )
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
                                                      true
                                                      (= v_0 0)
                                                    )
                                                    (= v_1 0)
                                                  )
                                                  (= v_2 0)
                                                )
                                                (= v_3 0)
                                              )
                                              (= v_4 0)
                                            )
                                            (= v_5 0)
                                          )
                                          (= v_6 0)
                                        )
                                        (= v_7 0)
                                      )
                                      (= v_8 0)
                                    )
                                    (= v_9 0)
                                  )
                                )
                                (and 
                                  (= v_12 (ff.add 0 v_0))
                                  true
                                )
                              )
                            )
                            (and 
                              (and 
                                (= v_13 (ite  (= 1 v_0) 1 0))
                                (and 
                                  (ite 
                                    (= v_13 1)
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
                                                        true
                                                        (= v_0 v_0)
                                                      )
                                                      (= v_1 1)
                                                    )
                                                    (= v_2 v_2)
                                                  )
                                                  (= v_3 v_3)
                                                )
                                                (= v_4 v_4)
                                              )
                                              (= v_5 v_5)
                                            )
                                            (= v_6 v_6)
                                          )
                                          (= v_7 v_7)
                                        )
                                        (= v_8 v_8)
                                      )
                                      (= v_9 v_9)
                                    )
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
                                                        true
                                                        (= v_0 v_0)
                                                      )
                                                      (= v_1 0)
                                                    )
                                                    (= v_2 v_2)
                                                  )
                                                  (= v_3 v_3)
                                                )
                                                (= v_4 v_4)
                                              )
                                              (= v_5 v_5)
                                            )
                                            (= v_6 v_6)
                                          )
                                          (= v_7 v_7)
                                        )
                                        (= v_8 v_8)
                                      )
                                      (= v_9 v_9)
                                    )
                                  )
                                  (and 
                                    (= v_24 (ff.add v_12 v_1))
                                    true
                                  )
                                )
                              )
                              (and 
                                (and 
                                  (= v_25 (ite  (= 2 v_0) 1 0))
                                  (and 
                                    (ite 
                                      (= v_25 1)
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
                                                          true
                                                          (= v_0 v_0)
                                                        )
                                                        (= v_1 v_1)
                                                      )
                                                      (= v_2 1)
                                                    )
                                                    (= v_3 v_3)
                                                  )
                                                  (= v_4 v_4)
                                                )
                                                (= v_5 v_5)
                                              )
                                              (= v_6 v_6)
                                            )
                                            (= v_7 v_7)
                                          )
                                          (= v_8 v_8)
                                        )
                                        (= v_9 v_9)
                                      )
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
                                                          true
                                                          (= v_0 v_0)
                                                        )
                                                        (= v_1 v_1)
                                                      )
                                                      (= v_2 0)
                                                    )
                                                    (= v_3 v_3)
                                                  )
                                                  (= v_4 v_4)
                                                )
                                                (= v_5 v_5)
                                              )
                                              (= v_6 v_6)
                                            )
                                            (= v_7 v_7)
                                          )
                                          (= v_8 v_8)
                                        )
                                        (= v_9 v_9)
                                      )
                                    )
                                    (and 
                                      (= v_36 (ff.add v_24 v_2))
                                      true
                                    )
                                  )
                                )
                                (and 
                                  (and 
                                    (= v_37 (ite  (= 3 v_0) 1 0))
                                    (and 
                                      (ite 
                                        (= v_37 1)
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
                                                            true
                                                            (= v_0 v_0)
                                                          )
                                                          (= v_1 v_1)
                                                        )
                                                        (= v_2 v_2)
                                                      )
                                                      (= v_3 1)
                                                    )
                                                    (= v_4 v_4)
                                                  )
                                                  (= v_5 v_5)
                                                )
                                                (= v_6 v_6)
                                              )
                                              (= v_7 v_7)
                                            )
                                            (= v_8 v_8)
                                          )
                                          (= v_9 v_9)
                                        )
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
                                                            true
                                                            (= v_0 v_0)
                                                          )
                                                          (= v_1 v_1)
                                                        )
                                                        (= v_2 v_2)
                                                      )
                                                      (= v_3 0)
                                                    )
                                                    (= v_4 v_4)
                                                  )
                                                  (= v_5 v_5)
                                                )
                                                (= v_6 v_6)
                                              )
                                              (= v_7 v_7)
                                            )
                                            (= v_8 v_8)
                                          )
                                          (= v_9 v_9)
                                        )
                                      )
                                      (and 
                                        (= v_48 (ff.add v_36 v_3))
                                        true
                                      )
                                    )
                                  )
                                  (and 
                                    (and 
                                      (= v_49 (ite  (= 4 v_0) 1 0))
                                      (and 
                                        (ite 
                                          (= v_49 1)
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
                                                              true
                                                              (= v_0 v_0)
                                                            )
                                                            (= v_1 v_1)
                                                          )
                                                          (= v_2 v_2)
                                                        )
                                                        (= v_3 v_3)
                                                      )
                                                      (= v_4 1)
                                                    )
                                                    (= v_5 v_5)
                                                  )
                                                  (= v_6 v_6)
                                                )
                                                (= v_7 v_7)
                                              )
                                              (= v_8 v_8)
                                            )
                                            (= v_9 v_9)
                                          )
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
                                                              true
                                                              (= v_0 v_0)
                                                            )
                                                            (= v_1 v_1)
                                                          )
                                                          (= v_2 v_2)
                                                        )
                                                        (= v_3 v_3)
                                                      )
                                                      (= v_4 0)
                                                    )
                                                    (= v_5 v_5)
                                                  )
                                                  (= v_6 v_6)
                                                )
                                                (= v_7 v_7)
                                              )
                                              (= v_8 v_8)
                                            )
                                            (= v_9 v_9)
                                          )
                                        )
                                        (and 
                                          (= v_60 (ff.add v_48 v_4))
                                          true
                                        )
                                      )
                                    )
                                    (and 
                                      (and 
                                        (= v_61 (ite  (= 5 v_0) 1 0))
                                        (and 
                                          (ite 
                                            (= v_61 1)
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
                                                                true
                                                                (= v_0 v_0)
                                                              )
                                                              (= v_1 v_1)
                                                            )
                                                            (= v_2 v_2)
                                                          )
                                                          (= v_3 v_3)
                                                        )
                                                        (= v_4 v_4)
                                                      )
                                                      (= v_5 1)
                                                    )
                                                    (= v_6 v_6)
                                                  )
                                                  (= v_7 v_7)
                                                )
                                                (= v_8 v_8)
                                              )
                                              (= v_9 v_9)
                                            )
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
                                                                true
                                                                (= v_0 v_0)
                                                              )
                                                              (= v_1 v_1)
                                                            )
                                                            (= v_2 v_2)
                                                          )
                                                          (= v_3 v_3)
                                                        )
                                                        (= v_4 v_4)
                                                      )
                                                      (= v_5 0)
                                                    )
                                                    (= v_6 v_6)
                                                  )
                                                  (= v_7 v_7)
                                                )
                                                (= v_8 v_8)
                                              )
                                              (= v_9 v_9)
                                            )
                                          )
                                          (and 
                                            (= v_72 (ff.add v_60 v_5))
                                            true
                                          )
                                        )
                                      )
                                      (and 
                                        (and 
                                          (= v_73 (ite  (= 6 v_0) 1 0))
                                          (and 
                                            (ite 
                                              (= v_73 1)
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
                                                                  true
                                                                  (= v_0 v_0)
                                                                )
                                                                (= v_1 v_1)
                                                              )
                                                              (= v_2 v_2)
                                                            )
                                                            (= v_3 v_3)
                                                          )
                                                          (= v_4 v_4)
                                                        )
                                                        (= v_5 v_5)
                                                      )
                                                      (= v_6 1)
                                                    )
                                                    (= v_7 v_7)
                                                  )
                                                  (= v_8 v_8)
                                                )
                                                (= v_9 v_9)
                                              )
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
                                                                  true
                                                                  (= v_0 v_0)
                                                                )
                                                                (= v_1 v_1)
                                                              )
                                                              (= v_2 v_2)
                                                            )
                                                            (= v_3 v_3)
                                                          )
                                                          (= v_4 v_4)
                                                        )
                                                        (= v_5 v_5)
                                                      )
                                                      (= v_6 0)
                                                    )
                                                    (= v_7 v_7)
                                                  )
                                                  (= v_8 v_8)
                                                )
                                                (= v_9 v_9)
                                              )
                                            )
                                            (and 
                                              (= v_84 (ff.add v_72 v_6))
                                              true
                                            )
                                          )
                                        )
                                        (and 
                                          (and 
                                            (= v_85 (ite  (= 7 v_0) 1 0))
                                            (and 
                                              (ite 
                                                (= v_85 1)
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
                                                                    true
                                                                    (= v_0 v_0)
                                                                  )
                                                                  (= v_1 v_1)
                                                                )
                                                                (= v_2 v_2)
                                                              )
                                                              (= v_3 v_3)
                                                            )
                                                            (= v_4 v_4)
                                                          )
                                                          (= v_5 v_5)
                                                        )
                                                        (= v_6 v_6)
                                                      )
                                                      (= v_7 1)
                                                    )
                                                    (= v_8 v_8)
                                                  )
                                                  (= v_9 v_9)
                                                )
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
                                                                    true
                                                                    (= v_0 v_0)
                                                                  )
                                                                  (= v_1 v_1)
                                                                )
                                                                (= v_2 v_2)
                                                              )
                                                              (= v_3 v_3)
                                                            )
                                                            (= v_4 v_4)
                                                          )
                                                          (= v_5 v_5)
                                                        )
                                                        (= v_6 v_6)
                                                      )
                                                      (= v_7 0)
                                                    )
                                                    (= v_8 v_8)
                                                  )
                                                  (= v_9 v_9)
                                                )
                                              )
                                              (and 
                                                (= v_96 (ff.add v_84 v_7))
                                                true
                                              )
                                            )
                                          )
                                          (and 
                                            (and 
                                              (= v_97 (ite  (= 8 v_0) 1 0))
                                              (and 
                                                (ite 
                                                  (= v_97 1)
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
                                                                      true
                                                                      (= v_0 v_0)
                                                                    )
                                                                    (= v_1 v_1)
                                                                  )
                                                                  (= v_2 v_2)
                                                                )
                                                                (= v_3 v_3)
                                                              )
                                                              (= v_4 v_4)
                                                            )
                                                            (= v_5 v_5)
                                                          )
                                                          (= v_6 v_6)
                                                        )
                                                        (= v_7 v_7)
                                                      )
                                                      (= v_8 1)
                                                    )
                                                    (= v_9 v_9)
                                                  )
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
                                                                      true
                                                                      (= v_0 v_0)
                                                                    )
                                                                    (= v_1 v_1)
                                                                  )
                                                                  (= v_2 v_2)
                                                                )
                                                                (= v_3 v_3)
                                                              )
                                                              (= v_4 v_4)
                                                            )
                                                            (= v_5 v_5)
                                                          )
                                                          (= v_6 v_6)
                                                        )
                                                        (= v_7 v_7)
                                                      )
                                                      (= v_8 0)
                                                    )
                                                    (= v_9 v_9)
                                                  )
                                                )
                                                (and 
                                                  (= v_108 (ff.add v_96 v_8))
                                                  true
                                                )
                                              )
                                            )
                                            (and 
                                              (= v_109 (ite  (= 9 v_0) 1 0))
                                              (and 
                                                (ite 
                                                  (= v_109 1)
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
                                                                      true
                                                                      (= v_0 v_0)
                                                                    )
                                                                    (= v_1 v_1)
                                                                  )
                                                                  (= v_2 v_2)
                                                                )
                                                                (= v_3 v_3)
                                                              )
                                                              (= v_4 v_4)
                                                            )
                                                            (= v_5 v_5)
                                                          )
                                                          (= v_6 v_6)
                                                        )
                                                        (= v_7 v_7)
                                                      )
                                                      (= v_8 v_8)
                                                    )
                                                    (= v_9 1)
                                                  )
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
                                                                      true
                                                                      (= v_0 v_0)
                                                                    )
                                                                    (= v_1 v_1)
                                                                  )
                                                                  (= v_2 v_2)
                                                                )
                                                                (= v_3 v_3)
                                                              )
                                                              (= v_4 v_4)
                                                            )
                                                            (= v_5 v_5)
                                                          )
                                                          (= v_6 v_6)
                                                        )
                                                        (= v_7 v_7)
                                                      )
                                                      (= v_8 v_8)
                                                    )
                                                    (= v_9 0)
                                                  )
                                                )
                                                (and 
                                                  (= v_120 (ff.add v_108 v_9))
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
                          true
                        )
                        (= v_121 v_0)
                      )
                      (= v_122 v_1)
                    )
                    (= v_123 v_2)
                  )
                  (= v_124 v_3)
                )
                (= v_125 v_4)
              )
              (= v_126 v_5)
            )
            (= v_127 v_6)
          )
          (= v_128 v_7)
        )
        (= v_129 v_8)
      )
      (= v_130 v_9)
    )
    (= v_131 v_120)
  )
)


(define-fun main ((v_0 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp) (v_47 FFp) (v_48 FFp) (v_49 FFp) (v_50 FFp) (v_51 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp)) Bool
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
                        (@Decoder_0 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40)
                        (= v_41 v_1)
                      )
                      (= v_42 v_2)
                    )
                    (= v_43 v_3)
                  )
                  (= v_44 v_4)
                )
                (= v_45 v_5)
              )
              (= v_46 v_6)
            )
            (= v_47 v_7)
          )
          (= v_48 v_8)
        )
        (= v_49 v_9)
      )
      (= v_50 v_10)
    )
    (= v_51 v_11)
  )
)


(assert 
  (main v_0 v_41 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50 v_51 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40)
)
