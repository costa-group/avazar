; modifications: 
; 

(set-logic QF_FF)
(define-sort FF0 () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-fun s_0 () FF0)
(declare-fun s_1 () FF0)
(declare-fun s_2 () FF0)
(declare-fun s_3 () FF0)
(declare-fun v_0 () FF0)
(declare-fun v_1 () FF0)
(declare-fun v_2 () FF0)
(declare-fun v_3 () FF0)
(declare-fun v_4 () FF0)
(declare-fun v_5 () FF0)
(declare-fun v_6 () FF0)
(declare-fun v_7 () FF0)
(assert (= (ff.add (as ff1 FF0) (ff.mul s_1 (as ff21888242871839275222246405745257275088548364400416034343698204186575808495616 FF0)) ) (ff.mul s_2  s_3 )))
(assert (= (as ff0 FF0) (ff.mul s_2  s_1 )))

(assert (and 
	(ite  (= (as ff0 FF0) v_0) (= v_1 (as ff0 FF0)) (= v_1 (as ff1 FF0))); trying other formulation
	(= v_1 (ite (= (as ff0 FF0) v_0) (as ff0 FF0) (as ff1 FF0))) ; v_1 is 0 if v_0 = 0, 1 otherwise 
	(ite (= v_1 (as ff1 FF0)) (and (and 
		; if
			; v_3 = v_2 --> apply in this case
			(= (ff.mul v_2 v_0) 1) true) 
			(= v_3 v_2) ; inv * in = 1
			
			; INSTEAD WE USE
			;(= (ff.mul v_3 v_0) (as ff1 FF0)) true) 


		) ;else
			(and true (= v_3 (as ff0 FF0)); inv = 0
		)
	)
	(= v_4 (ff.mul (as ff21888242871839275222246405745257275088548364400416034343698204186575808495616 FF0) v_0)) ; v_4 = -in
	(= v_5 (ff.mul (ff.mul v_4 v_3))) ; v_5 = -in * inv
	; We substitute v_4 by - v_0 everywhere
	
	; INSTEAD WE USE
	;(= v_5 (ff.mul (ff.mul (as ff21888242871839275222246405745257275088548364400416034343698204186575808495616 FF0) v_0) v_3)) ; v_5 = -in * inv
	(= v_6 (ff.add v_5 (as ff1 FF0))) ; v_6 = -in * inv + 1
	(= v_7 v_6) ; out = -in * inv + 1
))
(assert (= s_2 v_0))
(assert (not (= s_1 v_7)))
(check-sat)
