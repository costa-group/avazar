

template Num2Ternary(n) {
    signal input in;
    signal output {binary} out[n][2];
    var lc1=0;

    var e3=1;

    signal ternary_digits[n];
    for (var i = 0; i<n; i++) {
        ternary_digits[i] <-- (in \ e3) % 3;
        lc1 += ternary_digits[i] * e3;
        e3 *= 3;
        
                        out[i] <== Num2Bits(2)(ternary_digits[i]);
    }

    lc1 === in;
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


component main = Num2Ternary(2);
