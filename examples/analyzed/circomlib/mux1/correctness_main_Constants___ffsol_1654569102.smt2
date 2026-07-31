(set-logic QF_FF)
(define-sort FF0 () (_ FiniteField 18446744069414584321))
(declare-fun s_3 () FF0)
(declare-fun s_4 () FF0)
(declare-fun v_6 () FF0)
(declare-fun v_7 () FF0)
(assert (= (ff.add (as ff37 FF0) (ff.mul s_3 (as ff18446744069414584320 FF0)) ) (as ff0 FF0)))
(assert (= (ff.add (ff.mul s_4 (as ff18446744069414584320 FF0)) (as ff47 FF0) ) (as ff0 FF0)))
(define-fun @MultiMux1_0 ((macro_v_0 FF0) (macro_v_1 FF0) (macro_v_2 FF0) (macro_v_26 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_23 FF0) ) Bool
true)

(define-fun @Mux1_1 ((macro_v_0 FF0) (macro_v_1 FF0) (macro_v_2 FF0) (macro_v_40 FF0) (macro_v_33 FF0) (macro_v_34 FF0) (macro_v_35 FF0) (macro_v_36 FF0) ) Bool
true)

(define-fun @Num2Bits_2 ((macro_v_0 FF0) (macro_v_71 FF0) (macro_v_2 FF0) (macro_v_3 FF0) (macro_v_4 FF0) (macro_v_5 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_9 FF0) (macro_v_10 FF0) (macro_v_11 FF0) (macro_v_12 FF0) (macro_v_13 FF0) (macro_v_14 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_17 FF0) (macro_v_18 FF0) (macro_v_19 FF0) (macro_v_20 FF0) (macro_v_21 FF0) (macro_v_22 FF0) (macro_v_23 FF0) (macro_v_24 FF0) (macro_v_25 FF0) (macro_v_26 FF0) (macro_v_27 FF0) (macro_v_28 FF0) (macro_v_29 FF0) (macro_v_30 FF0) (macro_v_31 FF0) (macro_v_32 FF0) (macro_v_33 FF0) (macro_v_34 FF0) (macro_v_35 FF0) (macro_v_36 FF0) (macro_v_37 FF0) (macro_v_38 FF0) (macro_v_39 FF0) (macro_v_40 FF0) (macro_v_41 FF0) (macro_v_42 FF0) (macro_v_43 FF0) (macro_v_44 FF0) (macro_v_45 FF0) (macro_v_46 FF0) (macro_v_47 FF0) (macro_v_48 FF0) (macro_v_49 FF0) (macro_v_50 FF0) (macro_v_51 FF0) (macro_v_52 FF0) (macro_v_53 FF0) (macro_v_54 FF0) (macro_v_55 FF0) (macro_v_56 FF0) (macro_v_57 FF0) (macro_v_58 FF0) (macro_v_59 FF0) (macro_v_60 FF0) (macro_v_61 FF0) (macro_v_62 FF0) (macro_v_63 FF0) (macro_v_64 FF0) (macro_v_65 FF0) (macro_v_66 FF0) (macro_v_68 FF0) ) Bool
true)

(define-fun @Constants_3 ((macro_v_6 FF0) (macro_v_7 FF0) ) Bool
 (and  (and  (and  (! true :meta-data "array.new 2 %nondet") (and  (! true :meta-data "%felt_const_37 := 37") (and  (! true :meta-data "%felt_const_0_0 := 0") (and  (! true :meta-data "%0 := %felt_const_0_0") (and  (! true :meta-data "array.write %felt_const_37 %nondet[%0]") (and  (! true :meta-data "%felt_const_47 := 47") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! true :meta-data "%1 := %felt_const_1") (and  (! true :meta-data "array.write %felt_const_47 %nondet[%1]") (! true :meta-data "array.copy %nondet out") ) ) ) ) ) ) ) ) ) (= macro_v_6 37) ) (= macro_v_7 47) ) )

(define-fun @Main_4 ((macro_v_0 FF0) (macro_v_110 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_12 FF0) (macro_v_13 FF0) (macro_v_14 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_17 FF0) (macro_v_18 FF0) (macro_v_19 FF0) (macro_v_20 FF0) (macro_v_21 FF0) (macro_v_22 FF0) (macro_v_23 FF0) (macro_v_24 FF0) (macro_v_25 FF0) (macro_v_26 FF0) (macro_v_27 FF0) (macro_v_28 FF0) (macro_v_29 FF0) (macro_v_30 FF0) (macro_v_31 FF0) (macro_v_32 FF0) (macro_v_33 FF0) (macro_v_34 FF0) (macro_v_35 FF0) (macro_v_36 FF0) (macro_v_37 FF0) (macro_v_38 FF0) (macro_v_39 FF0) (macro_v_40 FF0) (macro_v_41 FF0) (macro_v_42 FF0) (macro_v_43 FF0) (macro_v_44 FF0) (macro_v_45 FF0) (macro_v_46 FF0) (macro_v_47 FF0) (macro_v_48 FF0) (macro_v_49 FF0) (macro_v_50 FF0) (macro_v_51 FF0) (macro_v_52 FF0) (macro_v_53 FF0) (macro_v_54 FF0) (macro_v_55 FF0) (macro_v_56 FF0) (macro_v_57 FF0) (macro_v_58 FF0) (macro_v_59 FF0) (macro_v_60 FF0) (macro_v_61 FF0) (macro_v_62 FF0) (macro_v_63 FF0) (macro_v_64 FF0) (macro_v_65 FF0) (macro_v_66 FF0) (macro_v_67 FF0) (macro_v_68 FF0) (macro_v_69 FF0) (macro_v_70 FF0) (macro_v_71 FF0) (macro_v_72 FF0) (macro_v_73 FF0) (macro_v_74 FF0) (macro_v_75 FF0) (macro_v_76 FF0) (macro_v_77 FF0) (macro_v_78 FF0) (macro_v_101 FF0) (macro_v_102 FF0) (macro_v_103 FF0) (macro_v_104 FF0) (macro_v_105 FF0) ) Bool
true)

(define-fun main ((macro_v_0 FF0) (macro_v_76 FF0) (macro_v_1 FF0) (macro_v_2 FF0) (macro_v_3 FF0) (macro_v_4 FF0) (macro_v_5 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_9 FF0) (macro_v_10 FF0) (macro_v_11 FF0) (macro_v_12 FF0) (macro_v_13 FF0) (macro_v_14 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_17 FF0) (macro_v_18 FF0) (macro_v_19 FF0) (macro_v_20 FF0) (macro_v_21 FF0) (macro_v_22 FF0) (macro_v_23 FF0) (macro_v_24 FF0) (macro_v_25 FF0) (macro_v_26 FF0) (macro_v_27 FF0) (macro_v_28 FF0) (macro_v_29 FF0) (macro_v_30 FF0) (macro_v_31 FF0) (macro_v_32 FF0) (macro_v_33 FF0) (macro_v_34 FF0) (macro_v_35 FF0) (macro_v_36 FF0) (macro_v_37 FF0) (macro_v_38 FF0) (macro_v_39 FF0) (macro_v_40 FF0) (macro_v_41 FF0) (macro_v_42 FF0) (macro_v_43 FF0) (macro_v_44 FF0) (macro_v_45 FF0) (macro_v_46 FF0) (macro_v_47 FF0) (macro_v_48 FF0) (macro_v_49 FF0) (macro_v_50 FF0) (macro_v_51 FF0) (macro_v_52 FF0) (macro_v_53 FF0) (macro_v_54 FF0) (macro_v_55 FF0) (macro_v_56 FF0) (macro_v_57 FF0) (macro_v_58 FF0) (macro_v_59 FF0) (macro_v_60 FF0) (macro_v_61 FF0) (macro_v_62 FF0) (macro_v_63 FF0) (macro_v_64 FF0) (macro_v_65 FF0) (macro_v_66 FF0) (macro_v_67 FF0) (macro_v_68 FF0) (macro_v_69 FF0) (macro_v_70 FF0) (macro_v_71 FF0) (macro_v_72 FF0) (macro_v_73 FF0) (macro_v_74 FF0) (macro_v_75 FF0) ) Bool
true)

(assert  (and  (and  (and  (! true :meta-data "array.new 2 %nondet") (and  (! true :meta-data "%felt_const_37 := 37") (and  (! true :meta-data "%felt_const_0_0 := 0") (and  (! true :meta-data "%0 := %felt_const_0_0") (and  (! true :meta-data "array.write %felt_const_37 %nondet[%0]") (and  (! true :meta-data "%felt_const_47 := 47") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! true :meta-data "%1 := %felt_const_1") (and  (! true :meta-data "array.write %felt_const_47 %nondet[%1]") (! true :meta-data "array.copy %nondet out") ) ) ) ) ) ) ) ) ) (= v_6 37) ) (= v_7 47) ) )
(assert true)
(assert (not (and  (= s_3 v_6)  (= s_4 v_7) )))
(check-sat)
