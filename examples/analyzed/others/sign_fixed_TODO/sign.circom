template SignFp() {
    signal input a;
    signal output {binary} sign;

    signal a_bits[64] <== Num2Bits_strict()(a);

    sign <== a_bits[0];
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

template CompConstant(ct) {
    signal input in[64];
    signal output out;

    signal parts[32];

    var clsb;
    var cmsb;
    var sl;
    var sm;

    signal sum[32];

    var e = 1;
    var i;

    for (i=0;i<32; i++) {
        clsb = (ct >> (i*2)) & 1;
        cmsb = (ct >> (i*2+1)) & 1;
        sl = in[i*2];
        sm = in[i*2+1];

        if ((cmsb==0)&&(clsb==0)) {
            parts[i] <== sm*e + sl*e -sm*sl*e;
        } else if ((cmsb==0)&&(clsb==1)) {
            parts[i] <== -e + e*sl + e*2*sm - e*sm*sl;
        } else if ((cmsb==1)&&(clsb==0)) {
            parts[i] <== e*sm*sl -e  +e*sm;
        } else {
            parts[i] <== e*sm*sl -e;
        }

        if (i==0) {
            sum[i] <== (1<<32)-1 + parts[i];
        } else {
            sum[i] <== sum[i-1] + parts[i];
        }

        e = e*2;
    }

    signal num2bits[33] <== Num2Bits(33)(sum[31]);

    for (var i = 0; i < 32; i++) {
        _ <== num2bits[i];
    }
    out <== num2bits[32];
}


template AliasCheck() {

    signal input in[64];

    signal compConstant <== CompConstant(-1)(in);
    compConstant === 0;
}

template Num2Bits_strict() {
    signal input in;
    signal output {binary} out[64];

    signal n2b[64] <== Num2Bits(64)(in);
    
    AliasCheck()(n2b);
    out <== n2b;
}


component main = SignFp();
