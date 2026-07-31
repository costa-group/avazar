include "comparators.circom";

template AliasCheckGoldilocks(){
    signal input in[64]; // input with the bit-decomposition
    
    // if all the 32 most-significant bits are 1 ==> all the 32 least-significant must be 0
    
    var most_sig_32_sum = 0;
    for (var i = 32; i < 64; i++){
        most_sig_32_sum += in[i];
    }
    
    
    var least_sig_32_sum = 0;
    for (var i = 0; i < 32; i++){
        least_sig_32_sum += in[i];
    }
    
    // check if all bits in most_sig_32_sum are 1
    signal all_one <== IsEqual()([most_sig_32_sum, 32]);
    
    // check if all bits in least_sig_32_sum are 0
    signal all_zero <== IsZero()(least_sig_32_sum);
    
    // all_one implies all_zero
    all_one * (1 - all_zero) === 0; 

}

template Main(){
    signal input in;
    signal output out[64] <== Num2Bits(64)(in);

    AliasCheckGoldilocks()(out);
}


component main = Main();
