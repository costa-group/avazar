template Decoder(w) {
    signal input inp;
    signal output out[w];
    signal output success;
    var lc=0;
    
    component checkZero[w];

    for (var i=0; i<w; i++) {
        checkZero[i] = IsZero();
        checkZero[i].in <== inp - i;
        out[i] <== checkZero[i].out;
        lc = lc + out[i];
    }

    lc ==> success;
}

template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}



component main = Decoder(4);