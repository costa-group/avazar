(set-logic QF_FF)
(define-sort FF0 () (_ FiniteField 18446744069414584321))
(declare-fun s_4 () FF0)
(declare-fun s_5 () FF0)
(declare-fun s_6 () FF0)
(declare-fun v_0 () FF0)
(declare-fun v_12 () FF0)
(declare-fun v_2 () FF0)
(declare-fun v_4 () FF0)
(declare-fun v_6 () FF0)
(declare-fun v_7 () FF0)
(declare-fun v_8 () FF0)
(declare-fun v_10 () FF0)
(assert (= (ff.add (ff.mul s_4 (as ff18446744069414584320 FF0)) (as ff1 FF0) ) (ff.mul s_5  s_6 )))
(assert (= (as ff0 FF0) (ff.mul s_5  s_4 )))
(define-fun @IsZero_0 ((macro_v_0 FF0) (macro_v_12 FF0) (macro_v_2 FF0) (macro_v_4 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_10 FF0) ) Bool
 (and  (and  (! true :meta-data "%felt_const_0 := 0") (and  (! (and  (= macro_v_2 (ite  (= 0 macro_v_0) 0 1)) (ff.range macro_v_2 0 1) ) :meta-data "%0 := bool.neq %felt_const_0 %arg0") (and  (! (ite  (= macro_v_2 1) (and  (and  (! true :meta-data "%felt_const_1_0 := 1") (and  (! (= (ff.mul macro_v_4 macro_v_0) 1) :meta-data "%5 := felt.div %felt_const_1_0 %arg0") (! true :meta-data "%1 := %5") ) ) (= macro_v_6 macro_v_4) ) (and  (and  (! true :meta-data "%felt_const_0_0 := 0") (! true :meta-data "%1 := %felt_const_0_0") ) (= macro_v_6 0) ) ) :meta-data "if (%0 == 1)") (and  (! (= macro_v_7 (ff.neg macro_v_0)) :meta-data "%2 := felt.neg %arg0") (and  (! (= macro_v_8 (ff.mul macro_v_7 macro_v_6)) :meta-data "%3 := felt.mul %2 %1") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! (= macro_v_10 (ff.add macro_v_8 1)) :meta-data "%4 := felt.add %3 %felt_const_1") (! true :meta-data "out := %4") ) ) ) ) ) ) ) (= macro_v_12 macro_v_10) ) )

(define-fun @IsEqual_1 ((macro_v_0 FF0) (macro_v_1 FF0) (macro_v_25 FF0) (macro_v_9 FF0) (macro_v_14 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_17 FF0) (macro_v_18 FF0) (macro_v_19 FF0) (macro_v_20 FF0) ) Bool
true)

(define-fun main ((macro_v_0 FF0) (macro_v_1 FF0) (macro_v_11 FF0) (macro_v_2 FF0) (macro_v_3 FF0) (macro_v_4 FF0) (macro_v_5 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_9 FF0) (macro_v_10 FF0) ) Bool
true)

(assert  (and  (and  (! true :meta-data "%felt_const_0 := 0") (and  (! (and  (= v_2 (ite  (= 0 v_0) 0 1)) (ff.range v_2 0 1) ) :meta-data "%0 := bool.neq %felt_const_0 %arg0") (and  (! (ite  (= v_2 1) (and  (and  (! true :meta-data "%felt_const_1_0 := 1") (and  (! (= (ff.mul v_4 v_0) 1) :meta-data "%5 := felt.div %felt_const_1_0 %arg0") (! true :meta-data "%1 := %5") ) ) (= v_6 v_4) ) (and  (and  (! true :meta-data "%felt_const_0_0 := 0") (! true :meta-data "%1 := %felt_const_0_0") ) (= v_6 0) ) ) :meta-data "if (%0 == 1)") (and  (! (= v_7 (ff.neg v_0)) :meta-data "%2 := felt.neg %arg0") (and  (! (= v_8 (ff.mul v_7 v_6)) :meta-data "%3 := felt.mul %2 %1") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! (= v_10 (ff.add v_8 1)) :meta-data "%4 := felt.add %3 %felt_const_1") (! true :meta-data "out := %4") ) ) ) ) ) ) ) (= v_12 v_10) ) )
(assert (= s_5 v_0))
(assert (not (= s_4 v_12)))
(check-sat)
