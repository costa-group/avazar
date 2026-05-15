pragma circom 2.0.0;

template RockPaperScissors(){
   signal input player1;
   signal input player2;
   // 2: rock, 3: paper, 5: scissors

   
   signal output winner;
   
   assert(player1 == 2 || player1 == 3 || player1 == 5);
   assert(player2 == 2 || player2 == 3 || player2 == 5);
   
   if (player1 == player2){
       winner <-- 0; // case tie
   } else if (player1 == 2 && player2 == 5){
       winner <-- 1;
   } else if (player1 == 3 && player2 == 2){
      winner <-- 1;
   } else if (player1 == 5 && player2 == 3){
      winner <-- 1;
   } else{
      winner <-- 2;
   }


}

component main = RockPaperScissors();
