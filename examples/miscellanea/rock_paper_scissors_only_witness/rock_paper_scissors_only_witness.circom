pragma circom 2.0.0;

template RockPaperScissors(){
   signal input player1;
   signal input player2;
   
   signal output winner;
   
   if (player1 == player2){
       winner <-- 2;
   } else if (player1 == 0 && player2 == 2){
       winner <-- 0;
   } else if (player1 == 1 && player2 == 0){
      winner <-- 0;
   } else if (player1 == 2 && player2 == 1){
      winner <-- 0;
   } else{
      winner <-- 1;
   }


}

component main = RockPaperScissors();
