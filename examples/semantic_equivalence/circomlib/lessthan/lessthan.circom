template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;
    signal n2b_in;
    signal n2b_out[n+1];

    n2b_in <== in[0]+ (1<<n) - in[1];
    
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n+1; i++) {
        n2b_out[i] <-- (n2b_in >> i) & 1;
        n2b_out[i] * (n2b_out[i] -1 ) === 0;
        lc1 += n2b_out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === n2b_in;

    out <== 1-n2b_out[n];
}


component main = LessThan(10);
