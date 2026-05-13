pragma circom 2.0.0;
include "../../circomlib/circuits/comparators.circom";


template igualdadRepetida(val){
	signal input in;
	signal output out;

	component cmp = IsEqual();
	cmp.in[0] <== in;
	cmp.in[1] <== val;
	out <== cmp.out;
}

template piedra_papel_tijera (){

	//Piedra -> 0, Papel-> 1, Tijera->2
	signal input jugador1;//Representa ele stado del jugador 1
	signal input jugador2;//Representa el estado del jugador 2
	signal output ganador;//Representa cual de los dos jugadores ha ganado, 0-> jugador1 ; 1->jugador2, 2 -> empate

	//Código en C
	//if(jugador1 == jugador2){ //Empate
	//	ganador <-- 2;
	//}
	//else if(jugador2 == 0 && jugador1 == 2){ //Gana jugador 2 con piedra
	//	ganador <--1;
	//}
	//else if(jugador1 == 0 && jugador2 == 2){ // Gana jugador 1 con piedra
	//	ganador <--0;
	//}
	//else if(jugador2 == 2 && jugador1 == 1){ //Gana jugadpr 2 con tijera
	//	ganador <--1;
	//}
	//else if(jugador1 == 2 && jugador2 == 1){ //Gana jugador 1 con tijera
	//	ganador <-- 0;
	//}
	//else if(jugador2 == 1 && jugador1 == 0){ //Gana jugador 2 ocn papel
	//	ganador <--1;
	//}
	//else if(jugador1 == 1 && jugador2 == 0){ // Gana jugador 1 con papel
	//	ganador <-- 0;
	//}
	//else{
	//	ganador <-- 1; //Valor no valido
	//}

	//Circuito con las restricciones

	
	signal eq;
	signal inv;
	signal out;
	signal j1 ;
	signal j2;	
	 
	//Comparaciones de cada jugador y estado
	
	//Jugador 1 con piedra
	component J1_0 = igualdadRepetida(0);
	J1_0.in <== jugador1; 
	
	//Jugador 1 con papel
	component J1_1 = igualdadRepetida(1);
	J1_1.in <== jugador1;

	//Jugador 1 con tijera
	component J1_2 = igualdadRepetida(2);
	J1_2.in <== jugador1;

	//Jugador 2 con piedra
	component J2_0 = igualdadRepetida(0);
	J2_0.in <== jugador2;

	//Jugador 2 con papel
	component J2_1 = igualdadRepetida(1);
	J2_1.in <== jugador2;

	//Jugador 2 con tijera
	component J2_2 = igualdadRepetida(2);
	J2_2.in <== jugador2;



	//Igualdad entre jugadores, es decir, empate
	signal eq0;
	signal eq1;
	signal eq2;

	eq0 <== (J1_0.out) * (J2_0.out);
	eq1 <== (J1_1.out) * (J2_1.out);
	eq2 <== (J1_2.out) * (J2_2.out);  
	eq <== eq0 + eq1 + eq2;       
	
	//Si fue empate, enotnces inv -> 0, si no lo hay inv-> 1        
        inv <== (1 - eq);


	//Como no pueod poner todo esto en un mismo output, guardo en j1 si este gana
	//J1 solo gana si se cumplen alguna de las siguientes combinaciones:
	signal j1_0;
	signal j1_1;
	signal j1_2;

	j1_0 <== (J1_0.out) * (J2_2.out) ;
	j1_1 <== (J1_1.out) * (J2_0.out) ;
	j1_2 <== (J1_2.out) * (J2_1.out);

	j1 <== j1_0 + j1_1 + j1_2;
	

	//Lo mismo pasa con j2:
	signal j2_0;
	signal j2_1;
	signal j2_2;

	j2_0 <== (J1_0.out) * (J2_1.out);
	j2_1 <== (J1_1.out) * (J2_2.out);
	j2_2 <== (J1_2.out) * (J2_0.out);

	j2 <== j2_0 + j2_1 + j2_2;
	
	//Ahora tenemos si tenemos un empate, o si en caso de no haberlo, que jugador ha ganado
	out <== (j2 * 1) + (j1 * 0); //Se puede simplificar
	
	ganador <== ((1-inv) * 2) + (out * inv);
}	


component main = piedra_papel_tijera();
	



	
