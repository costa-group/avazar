(set-logic QF_FF)
(define-sort FF0 () (_ FiniteField 18446744069414584321))
(declare-fun s_16 () FF0)
(declare-fun s_17 () FF0)
(declare-fun s_18 () FF0)
(declare-fun v_0 () FF0)
(declare-fun v_12 () FF0)
(declare-fun v_2 () FF0)
(declare-fun v_4 () FF0)
(declare-fun v_6 () FF0)
(declare-fun v_7 () FF0)
(declare-fun v_8 () FF0)
(declare-fun v_10 () FF0)
(assert (= (ff.add (ff.mul s_16 (as ff18446744069414584320 FF0)) (as ff1 FF0) ) (ff.mul s_17  s_18 )))
(assert (= (as ff0 FF0) (ff.mul s_17  s_16 )))
(define-fun @IsZero_0 ((macro_v_0 FF0) (macro_v_12 FF0) (macro_v_2 FF0) (macro_v_4 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_10 FF0) ) Bool
 (and  (and  (! true :meta-data "%felt_const_0 := 0") (and  (! (and  (= macro_v_2 (ite  (= 0 macro_v_0) 0 1)) (ff.range macro_v_2 0 1) ) :meta-data "%0 := bool.neq %felt_const_0 %arg0") (and  (! (ite  (= macro_v_2 1) (and  (and  (! true :meta-data "%felt_const_1_0 := 1") (and  (! (= (ff.mul macro_v_4 macro_v_0) 1) :meta-data "%5 := felt.div %felt_const_1_0 %arg0") (! true :meta-data "%1 := %5") ) ) (= macro_v_6 macro_v_4) ) (and  (and  (! true :meta-data "%felt_const_0_0 := 0") (! true :meta-data "%1 := %felt_const_0_0") ) (= macro_v_6 0) ) ) :meta-data "if (%0 == 1)") (and  (! (= macro_v_7 (ff.neg macro_v_0)) :meta-data "%2 := felt.neg %arg0") (and  (! (= macro_v_8 (ff.mul macro_v_7 macro_v_6)) :meta-data "%3 := felt.mul %2 %1") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! (= macro_v_10 (ff.add macro_v_8 1)) :meta-data "%4 := felt.add %3 %felt_const_1") (! true :meta-data "out := %4") ) ) ) ) ) ) ) (= macro_v_12 macro_v_10) ) )

(define-fun @Decoder_1 ((macro_v_0 FF0) (macro_v_131 FF0) (macro_v_132 FF0) (macro_v_133 FF0) (macro_v_134 FF0) (macro_v_135 FF0) (macro_v_18 FF0) (macro_v_27 FF0) (macro_v_28 FF0) (macro_v_29 FF0) (macro_v_30 FF0) (macro_v_31 FF0) (macro_v_32 FF0) (macro_v_33 FF0) (macro_v_41 FF0) (macro_v_45 FF0) (macro_v_54 FF0) (macro_v_55 FF0) (macro_v_56 FF0) (macro_v_57 FF0) (macro_v_58 FF0) (macro_v_59 FF0) (macro_v_60 FF0) (macro_v_68 FF0) (macro_v_72 FF0) (macro_v_81 FF0) (macro_v_82 FF0) (macro_v_83 FF0) (macro_v_84 FF0) (macro_v_85 FF0) (macro_v_86 FF0) (macro_v_87 FF0) (macro_v_95 FF0) (macro_v_99 FF0) (macro_v_108 FF0) (macro_v_109 FF0) (macro_v_110 FF0) (macro_v_111 FF0) (macro_v_112 FF0) (macro_v_113 FF0) (macro_v_114 FF0) (macro_v_122 FF0) ) Bool
true)

(define-fun main ((macro_v_0 FF0) (macro_v_42 FF0) (macro_v_43 FF0) (macro_v_44 FF0) (macro_v_45 FF0) (macro_v_46 FF0) (macro_v_1 FF0) (macro_v_2 FF0) (macro_v_3 FF0) (macro_v_4 FF0) (macro_v_5 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_9 FF0) (macro_v_10 FF0) (macro_v_11 FF0) (macro_v_12 FF0) (macro_v_13 FF0) (macro_v_14 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_17 FF0) (macro_v_18 FF0) (macro_v_19 FF0) (macro_v_20 FF0) (macro_v_21 FF0) (macro_v_22 FF0) (macro_v_23 FF0) (macro_v_24 FF0) (macro_v_25 FF0) (macro_v_26 FF0) (macro_v_27 FF0) (macro_v_28 FF0) (macro_v_29 FF0) (macro_v_30 FF0) (macro_v_31 FF0) (macro_v_32 FF0) (macro_v_33 FF0) (macro_v_34 FF0) (macro_v_35 FF0) (macro_v_36 FF0) (macro_v_37 FF0) (macro_v_38 FF0) (macro_v_39 FF0) (macro_v_40 FF0) (macro_v_41 FF0) ) Bool
true)

(assert  (and  (and  (! true :meta-data "%felt_const_0 := 0") (and  (! (and  (= v_2 (ite  (= 0 v_0) 0 1)) (ff.range v_2 0 1) ) :meta-data "%0 := bool.neq %felt_const_0 %arg0") (and  (! (ite  (= v_2 1) (and  (and  (! true :meta-data "%felt_const_1_0 := 1") (and  (! (= (ff.mul v_4 v_0) 1) :meta-data "%5 := felt.div %felt_const_1_0 %arg0") (! true :meta-data "%1 := %5") ) ) (= v_6 v_4) ) (and  (and  (! true :meta-data "%felt_const_0_0 := 0") (! true :meta-data "%1 := %felt_const_0_0") ) (= v_6 0) ) ) :meta-data "if (%0 == 1)") (and  (! (= v_7 (ff.neg v_0)) :meta-data "%2 := felt.neg %arg0") (and  (! (= v_8 (ff.mul v_7 v_6)) :meta-data "%3 := felt.mul %2 %1") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! (= v_10 (ff.add v_8 1)) :meta-data "%4 := felt.add %3 %felt_const_1") (! true :meta-data "out := %4") ) ) ) ) ) ) ) (= v_12 v_10) ) )
(assert (= s_17 v_0))
(assert (not (= s_16 v_12)))
(check-sat)
