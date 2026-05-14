pragma circom 2.0.0;
include "../../circomlib/circuits/comparators.circom";


template EqualToVal(val){
	signal input in;
	signal output out;

	component cmp = IsEqual();
	cmp.in[0] <== in;
	cmp.in[1] <== val;
	out <== cmp.out;
}

template RockPaperScissors (){

	//Rock -> 0, Paper -> 1, Scissors -> 2
	signal input player1;
	signal input player2;
	signal output winner;
	
	signal eq;
	signal inv;
	signal out;
	signal j1;
	signal j2;	
	 
	// Comparisons of the possible state of each player
	
	// Player1 -> Rock
	component J1_0 = EqualToVal(0);
	J1_0.in <== player1; 
	
	// Player1 -> Paper
	component J1_1 = EqualToVal(1);
	J1_1.in <== player1;

	// Player1 -> Scissors
	component J1_2 = EqualToVal(2);
	J1_2.in <== player1;

	component J2_0 = EqualToVal(0);
	J2_0.in <== player2;

	component J2_1 = EqualToVal(1);
	J2_1.in <== player2;

	component J2_2 = EqualToVal(2);
	J2_2.in <== player2;



	// Ties between players
	signal eq0;
	signal eq1;
	signal eq2;

	eq0 <== (J1_0.out) * (J2_0.out);
	eq1 <== (J1_1.out) * (J2_1.out);
	eq2 <== (J1_2.out) * (J2_2.out);  
	eq <== eq0 + eq1 + eq2;       
	
	// Tie implies inv -> 0. Otherwise, inv-> 1        
        inv <== (1 - eq);


	signal j1_0;
	signal j1_1;
	signal j1_2;

	j1_0 <== (J1_0.out) * (J2_2.out) ;
	j1_1 <== (J1_1.out) * (J2_0.out) ;
	j1_2 <== (J1_2.out) * (J2_1.out);

	j1 <== j1_0 + j1_1 + j1_2;
	

	signal j2_0;
	signal j2_1;
	signal j2_2;

	j2_0 <== (J1_0.out) * (J2_1.out);
	j2_1 <== (J1_1.out) * (J2_2.out);
	j2_2 <== (J1_2.out) * (J2_0.out);

	j2 <== j2_0 + j2_1 + j2_2;
	
	// Determining the winner
	out <== (j2 * 1) + (j1 * 0);
	
	winner <== ((1-inv) * 2) + (out * inv);
}	


component main = RockPaperScissors();