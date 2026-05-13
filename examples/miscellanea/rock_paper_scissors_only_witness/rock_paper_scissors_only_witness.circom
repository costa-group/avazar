pragma circom 2.0.0;

template Juego(){
   signal input jugador1;
   signal input jugador2;
   
   signal output ganador;
   
   if (jugador1 == jugador2){
       ganador <-- 2;
   } else if (jugador1 == 0 && jugador2 == 2){
       ganador <-- 0;
   } else if (jugador1 == 1 && jugador2 == 0){
      ganador <-- 0;
   } else if (jugador1 == 2 && jugador2 == 1){
      ganador <-- 0;
   } else{
      ganador <-- 1;
   }


}

component main = Juego();
