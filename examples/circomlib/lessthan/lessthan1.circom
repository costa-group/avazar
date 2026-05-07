template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    out <-- in[0] < in[1];
}


component main = LessThan(10);
