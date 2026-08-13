function maxbits(){
    var n = 1;
    var r = 1;
    while(2 * n > n){
        n = n * 2;
        r = r + 1;
    }
    return r + 1;
}


function num2bits_function(n, nBits) {
    var bits[maxbits()];
    var acc = n;

    for (var i = 0; i < nBits; i++) {
        bits[i] = acc % 2;
        acc = acc \ 2; // In Circom, \ performs integer division
    }

    return bits;
}


template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in;
}


template IsZero() {
    input signal in;
    output signal {binary} out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}



/*
*** IsEqual(): template that receives two inputs in[0] and in[1] representing field values and returns 1 if in[0] == in[1], 0 otherwise.
        - Inputs: in[2] -> array of 2 field values
        - Outputs: out -> in[0] == in[1]
                          satisfies tag binary
         
    Example: IsEqual()([5, 2]) = 0, IsZero()([2, 2]) = 0
          
*/

template IsEqual() {
    input signal in[2];
    output signal {binary} out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}


template GeneralAliasCheck(){

   // First we bitify the value of p-1. As it is a constant, we call to the auxiliar function to_bits
   var bits = maxbits();
   var p_to_bits[bits] = num2bits_function(-1, bits);

   signal input in[bits];
   
   
   // consider the most significant bit and open the first group
   var prev_bit = p_to_bits[bits - 1];
   var sum_group = in[bits - 1];
   var size_window = 1;
   
   var num_zeros = 0;
   var num_ones = 0;
   
   signal conds_one[bits];
   signal conds_zero[bits];
   

   
   
   for (var i = bits - 2; i >= 0; i--){
      if (prev_bit == p_to_bits[i]){
         // does not change the bit, continue in the same group. We update the sum adding the new value
         sum_group += in[i];
         size_window += 1;
      }
      
      else{
         // the bit changes, we close the previous group adding the condition and open a new window
         if (prev_bit == 0){
            // we close a window of 0s
            if (size_window > 1){
               conds_zero[num_zeros] <== IsZero()(sum_group);
            } else{
               conds_zero[num_zeros] <== 1 - sum_group;
            }

            num_zeros += 1;
         } else{
            // we close a window of 1s
            if (size_window > 1){
               conds_one[num_ones] <== IsEqual()([sum_group, size_window]);
            } else{
               conds_one[num_ones] <== sum_group;
            }

            num_ones += 1;
         }
         
         // we open the new window
         prev_bit = p_to_bits[i];
         sum_group = in[i];
         size_window = 1;
      }

   }
   
   // Finally we close the last window
   if (prev_bit == 0){
      // we close a window of 0s
      if (size_window > 1){
         conds_zero[num_zeros] <== IsZero()(sum_group);
      } else{
         conds_zero[num_zeros] <== 1 - sum_group;
      }

      num_zeros += 1;
     
   } else{
      // we close a window of 1s
      if (size_window > 1){
         conds_one[num_ones] <== IsEqual()([sum_group, size_window]);
      } else{
         conds_one[num_ones] <== sum_group;
      }
      
      num_ones += 1;

   }


   // Now we generate the condition stating that the in should be smaller or equal than p-1
   signal acum_result[num_zeros + num_ones];
   var index_zeros = num_zeros - 1;
   var index_ones = num_ones - 1;

   if (prev_bit == 0){ // number with last window being a 0
      acum_result[0] <== 1 - conds_zero[index_zeros];
      prev_bit = 1;
      index_zeros -= 1;
   } else if (prev_bit == 1){
      acum_result[0] <== conds_one[index_ones];
      prev_bit = 0;
      index_ones -= 1;
   }

   var i = 1;

   while(index_zeros >= 0 || index_ones >= 0){
      if (prev_bit == 0){ // number with last window being a 0
         acum_result[i] <== (1 - conds_zero[index_zeros]) + acum_result[i-1] ;
         prev_bit = 1;
         index_zeros -= 1;
      } else if (prev_bit == 1){
         acum_result[i] <== conds_one[index_ones] * acum_result[i-1];
         prev_bit = 0;
         index_ones -= 1;
      }
      i += 1;
   }
   
   // We add the condition stating that the result should be <= p-1
   acum_result[num_zeros + num_ones - 1] === 0;


}


template Main(){
    signal input in;
    signal output out[maxbits()] <== Num2Bits(maxbits())(in);

    GeneralAliasCheck()(out);
}


component main = Main();