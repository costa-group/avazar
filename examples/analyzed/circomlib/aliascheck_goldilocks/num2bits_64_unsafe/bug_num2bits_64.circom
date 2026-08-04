include "bitify.circom";


template Main(){
    signal input in;
    signal output out[64] <== Num2Bits(64)(in);

}


component main = Main();
