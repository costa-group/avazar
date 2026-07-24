template SignFp() {
    signal input a;
    signal output {binary} sign;

    sign <-- a % 2;
    sign * (1 - sign) === 0;
    signal q <-- a \ 2;
    a === 2 * q + sign;
}


component main = SignFp();
