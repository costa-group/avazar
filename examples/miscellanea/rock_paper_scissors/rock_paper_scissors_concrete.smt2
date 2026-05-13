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
(declare-const v_86 FFp)
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


(define-fun @igualdadRepetida_2 ((v_0 FFp) (v_10 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp)) Bool
  (and 
    (and 
      (and 
        (@IsEqual_1 v_0 0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9)
        true
      )
      true
    )
    (= v_10 v_1)
  )
)


(define-fun @igualdadRepetida_3 ((v_0 FFp) (v_10 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp)) Bool
  (and 
    (and 
      (and 
        (@IsEqual_1 v_0 1 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9)
        true
      )
      true
    )
    (= v_10 v_1)
  )
)


(define-fun @igualdadRepetida_4 ((v_0 FFp) (v_10 FFp) (v_1 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp)) Bool
  (and 
    (and 
      (and 
        (@IsEqual_1 v_0 2 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9)
        true
      )
      true
    )
    (= v_10 v_1)
  )
)


(define-fun @piedra_papel_tijera_5 ((v_0 FFp) (v_1 FFp) (v_85 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp) (v_47 FFp) (v_48 FFp) (v_49 FFp) (v_50 FFp) (v_51 FFp) (v_52 FFp) (v_53 FFp) (v_54 FFp) (v_55 FFp) (v_56 FFp) (v_57 FFp) (v_58 FFp) (v_59 FFp) (v_60 FFp) (v_61 FFp) (v_62 FFp) (v_63 FFp) (v_64 FFp) (v_65 FFp) (v_66 FFp) (v_67 FFp) (v_68 FFp) (v_69 FFp) (v_70 FFp) (v_71 FFp) (v_72 FFp) (v_73 FFp) (v_74 FFp) (v_75 FFp) (v_76 FFp) (v_77 FFp) (v_78 FFp) (v_79 FFp) (v_80 FFp) (v_81 FFp) (v_82 FFp) (v_83 FFp) (v_84 FFp)) Bool
  (and 
    (and 
      (and 
        (@igualdadRepetida_2 v_0 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11)
        true
      )
      (and 
        (and 
          (@igualdadRepetida_3 v_0 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21)
          true
        )
        (and 
          (and 
            (@igualdadRepetida_4 v_0 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31)
            true
          )
          (and 
            (and 
              (@igualdadRepetida_2 v_1 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41)
              true
            )
            (and 
              (and 
                (@igualdadRepetida_3 v_1 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50 v_51)
                true
              )
              (and 
                (and 
                  (@igualdadRepetida_4 v_1 v_52 v_53 v_54 v_55 v_56 v_57 v_58 v_59 v_60 v_61)
                  true
                )
                (and 
                  (= v_62 (ff.mul v_2 v_32))
                  (and 
                    (= v_63 (ff.mul v_12 v_42))
                    (and 
                      (= v_64 (ff.mul v_22 v_52))
                      (and 
                        (= v_65 (ff.add v_62 v_63))
                        (and 
                          (= v_66 (ff.add v_65 v_64))
                          (and 
                            (= v_67 (ff.sub 1 v_66))
                            (and 
                              (= v_68 (ff.mul v_2 v_52))
                              (and 
                                (= v_69 (ff.mul v_12 v_32))
                                (and 
                                  (= v_70 (ff.mul v_22 v_42))
                                  (and 
                                    (= v_71 (ff.add v_68 v_69))
                                    (and 
                                      (= v_72 (ff.add v_71 v_70))
                                      (and 
                                        (= v_73 (ff.mul v_2 v_42))
                                        (and 
                                          (= v_74 (ff.mul v_12 v_52))
                                          (and 
                                            (= v_75 (ff.mul v_22 v_32))
                                            (and 
                                              (= v_76 (ff.add v_73 v_74))
                                              (and 
                                                (= v_77 (ff.add v_76 v_75))
                                                (and 
                                                  (= v_78 (ff.mul v_77 1))
                                                  (and 
                                                    (= v_79 (ff.mul v_72 0))
                                                    (and 
                                                      (= v_80 (ff.add v_78 v_79))
                                                      (and 
                                                        (= v_81 (ff.sub 1 v_67))
                                                        (and 
                                                          (= v_82 (ff.mul v_81 2))
                                                          (and 
                                                            (= v_83 (ff.mul v_80 v_67))
                                                            (and 
                                                              (= v_84 (ff.add v_82 v_83))
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
    (= v_85 v_84)
  )
)


(define-fun main ((v_0 FFp) (v_1 FFp) (v_86 FFp) (v_2 FFp) (v_3 FFp) (v_4 FFp) (v_5 FFp) (v_6 FFp) (v_7 FFp) (v_8 FFp) (v_9 FFp) (v_10 FFp) (v_11 FFp) (v_12 FFp) (v_13 FFp) (v_14 FFp) (v_15 FFp) (v_16 FFp) (v_17 FFp) (v_18 FFp) (v_19 FFp) (v_20 FFp) (v_21 FFp) (v_22 FFp) (v_23 FFp) (v_24 FFp) (v_25 FFp) (v_26 FFp) (v_27 FFp) (v_28 FFp) (v_29 FFp) (v_30 FFp) (v_31 FFp) (v_32 FFp) (v_33 FFp) (v_34 FFp) (v_35 FFp) (v_36 FFp) (v_37 FFp) (v_38 FFp) (v_39 FFp) (v_40 FFp) (v_41 FFp) (v_42 FFp) (v_43 FFp) (v_44 FFp) (v_45 FFp) (v_46 FFp) (v_47 FFp) (v_48 FFp) (v_49 FFp) (v_50 FFp) (v_51 FFp) (v_52 FFp) (v_53 FFp) (v_54 FFp) (v_55 FFp) (v_56 FFp) (v_57 FFp) (v_58 FFp) (v_59 FFp) (v_60 FFp) (v_61 FFp) (v_62 FFp) (v_63 FFp) (v_64 FFp) (v_65 FFp) (v_66 FFp) (v_67 FFp) (v_68 FFp) (v_69 FFp) (v_70 FFp) (v_71 FFp) (v_72 FFp) (v_73 FFp) (v_74 FFp) (v_75 FFp) (v_76 FFp) (v_77 FFp) (v_78 FFp) (v_79 FFp) (v_80 FFp) (v_81 FFp) (v_82 FFp) (v_83 FFp) (v_84 FFp) (v_85 FFp)) Bool
  (and 
    (@piedra_papel_tijera_5 v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50 v_51 v_52 v_53 v_54 v_55 v_56 v_57 v_58 v_59 v_60 v_61 v_62 v_63 v_64 v_65 v_66 v_67 v_68 v_69 v_70 v_71 v_72 v_73 v_74 v_75 v_76 v_77 v_78 v_79 v_80 v_81 v_82 v_83 v_84 v_85)
    (= v_86 v_2)
  )
)


(assert 
  (main v_0 v_1 v_86 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32 v_33 v_34 v_35 v_36 v_37 v_38 v_39 v_40 v_41 v_42 v_43 v_44 v_45 v_46 v_47 v_48 v_49 v_50 v_51 v_52 v_53 v_54 v_55 v_56 v_57 v_58 v_59 v_60 v_61 v_62 v_63 v_64 v_65 v_66 v_67 v_68 v_69 v_70 v_71 v_72 v_73 v_74 v_75 v_76 v_77 v_78 v_79 v_80 v_81 v_82 v_83 v_84 v_85)
)
