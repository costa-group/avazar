(set-logic QF_FF)
(define-sort FF0 () (_ FiniteField 18446744069414584321))
(declare-fun s_1 () FF0)
(declare-fun s_2 () FF0)
(declare-fun s_3 () FF0)
(declare-fun v_0 () FF0)
(declare-fun v_5 () FF0)
(declare-fun v_2 () FF0)
(declare-fun v_3 () FF0)
(assert (= (as ff0 FF0) (ff.mul (ff.add (as ff1 FF0) (ff.mul s_1 (as ff18446744069414584320 FF0)) ) s_1 )))
(assert (= (ff.add (ff.mul s_3 (as ff2 FF0)) s_1 (ff.mul s_2 (as ff18446744069414584320 FF0)) ) (as ff0 FF0)))
(define-fun @SignFp_0 ((macro_v_0 FF0) (macro_v_5 FF0) (macro_v_2 FF0) (macro_v_3 FF0) ) Bool
 (and  (and  (! true :meta-data "%felt_const_2 := 2") (and  (! (and  (= macro_v_0 (ff.add (ff.mul macro_v_2 2) macro_v_3)) (ff.range macro_v_3 0 1) ) :meta-data "%0 := felt.uimod %arg0 %felt_const_2") (! true :meta-data "sign := %0") ) ) (= macro_v_5 macro_v_3) ) )

(define-fun main ((macro_v_0 FF0) (macro_v_4 FF0) (macro_v_1 FF0) (macro_v_2 FF0) (macro_v_3 FF0) ) Bool
true)

(assert  (and  (and  (! true :meta-data "%felt_const_2 := 2") (and  (! (and  (= v_0 (ff.add (ff.mul v_2 2) v_3)) (ff.range v_3 0 1) ) :meta-data "%0 := felt.uimod %arg0 %felt_const_2") (! true :meta-data "sign := %0") ) ) (= v_5 v_3) ) )
(assert (= s_2 v_0))
(assert (not (= s_1 v_5)))
(check-sat)
