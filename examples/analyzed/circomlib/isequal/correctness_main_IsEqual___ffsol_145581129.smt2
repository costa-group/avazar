(set-logic QF_FF)
(define-sort FF0 () (_ FiniteField 18446744069414584321))
(declare-fun s_1 () FF0)
(declare-fun s_2 () FF0)
(declare-fun s_3 () FF0)
(declare-fun s_5 () FF0)
(declare-fun s_4 () FF0)
(declare-fun v_0 () FF0)
(declare-fun v_1 () FF0)
(declare-fun v_25 () FF0)
(declare-fun v_9 () FF0)
(declare-fun v_14 () FF0)
(declare-fun v_15 () FF0)
(declare-fun v_16 () FF0)
(declare-fun v_17 () FF0)
(declare-fun v_18 () FF0)
(declare-fun v_19 () FF0)
(declare-fun v_20 () FF0)
(assert (= (ff.add (ff.mul s_2 (as ff18446744069414584320 FF0)) (ff.mul s_5 (as ff18446744069414584320 FF0)) s_3 ) (as ff0 FF0)))
(assert (= (ff.add s_4 (ff.mul s_1 (as ff18446744069414584320 FF0)) ) (as ff0 FF0)))
(define-fun @IsZero_0 ((macro_v_0 FF0) (macro_v_12 FF0) (macro_v_2 FF0) (macro_v_4 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_10 FF0) ) Bool
true)

(define-fun @IsEqual_1 ((macro_v_0 FF0) (macro_v_1 FF0) (macro_v_25 FF0) (macro_v_9 FF0) (macro_v_14 FF0) (macro_v_15 FF0) (macro_v_16 FF0) (macro_v_17 FF0) (macro_v_18 FF0) (macro_v_19 FF0) (macro_v_20 FF0) ) Bool
 (and  (and  (! true :meta-data "%c1 := 1") (and  (! true :meta-data "%pod_0_@count := %c1") (and  (! true :meta-data "%pod_0_@comp_@out := 0") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! true :meta-data "%0 := %felt_const_1") (and  (! true :meta-data "array.read %arg0[%0] %1") (and  (! true :meta-data "%felt_const_0 := 0") (and  (! true :meta-data "%2 := %felt_const_0") (and  (! true :meta-data "array.read %arg0[%2] %3") (and  (! (= macro_v_9 (ff.sub macro_v_1 macro_v_0)) :meta-data "%4 := felt.sub %1 %3") (and  (! true :meta-data "isz.in := %4") (and  (! true :meta-data "%5 := %pod_0_@count") (and  (! true :meta-data "%c1_2 := 1") (and  (! true :meta-data "%6 := felt.sub %5 %c1_2") (and  (! true :meta-data "%c0 := 0") (and  (! true :meta-data "%7 := bool.eq %6 %c0") (and  (! (and  (! (@IsZero_0 macro_v_9 macro_v_14 macro_v_15 macro_v_16 macro_v_17 macro_v_18 macro_v_19 macro_v_20) :meta-data "call @IsZero_0 (isz.in) to isz.out") (! true :meta-data "%pod_0_@comp_@out := isz.out") ) :meta-data "if (%7 == 1)") (and  (! true :meta-data "%8_@out := %pod_0_@comp_@out") (and  (! true :meta-data "%9 := %8_@out") (! true :meta-data "out := %9") ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) (= macro_v_25 macro_v_14) ) )

(define-fun main ((macro_v_0 FF0) (macro_v_1 FF0) (macro_v_11 FF0) (macro_v_2 FF0) (macro_v_3 FF0) (macro_v_4 FF0) (macro_v_5 FF0) (macro_v_6 FF0) (macro_v_7 FF0) (macro_v_8 FF0) (macro_v_9 FF0) (macro_v_10 FF0) ) Bool
true)

(assert  (and  (and  (! true :meta-data "%c1 := 1") (and  (! true :meta-data "%pod_0_@count := %c1") (and  (! true :meta-data "%pod_0_@comp_@out := 0") (and  (! true :meta-data "%felt_const_1 := 1") (and  (! true :meta-data "%0 := %felt_const_1") (and  (! true :meta-data "array.read %arg0[%0] %1") (and  (! true :meta-data "%felt_const_0 := 0") (and  (! true :meta-data "%2 := %felt_const_0") (and  (! true :meta-data "array.read %arg0[%2] %3") (and  (! (= v_9 (ff.sub v_1 v_0)) :meta-data "%4 := felt.sub %1 %3") (and  (! true :meta-data "isz.in := %4") (and  (! true :meta-data "%5 := %pod_0_@count") (and  (! true :meta-data "%c1_2 := 1") (and  (! true :meta-data "%6 := felt.sub %5 %c1_2") (and  (! true :meta-data "%c0 := 0") (and  (! true :meta-data "%7 := bool.eq %6 %c0") (and  (! (and  (! (@IsZero_0 v_9 v_14 v_15 v_16 v_17 v_18 v_19 v_20) :meta-data "call @IsZero_0 (isz.in) to isz.out") (! true :meta-data "%pod_0_@comp_@out := isz.out") ) :meta-data "if (%7 == 1)") (and  (! true :meta-data "%8_@out := %pod_0_@comp_@out") (and  (! true :meta-data "%9 := %8_@out") (! true :meta-data "out := %9") ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) (= v_25 v_14) ) )
(assert (=> (= s_5 "v_9") (= s_4 "v_14")))
(assert (and  (= s_2 v_0)  (= s_3 v_1) ))
(assert (not (= s_1 v_25)))
(check-sat)
