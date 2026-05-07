/*
    Copyright 2018 0KIMS association.

    This file is part of circom (Zero Knowledge Circuit Compiler).

    circom is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    circom is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with circom. If not, see <https://www.gnu.org/licenses/>.
*/
pragma circom 2.0.0;

template MultiMux2(n) {
    signal input c[4];  // Constants
    signal input s[2];   // Selector
    signal output out;

    signal a10;
    signal a1;
    signal a0;
    signal a;

    signal  s10;
    s10 <== s[1] * s[0];
    a10 <==  ( c[ 3]-c[ 2]-c[ 1]+c[ 0] ) * s10;
    a1 <==  ( c[ 2]-c[ 0] ) * s[1];
    a0 <==  ( c[ 1]-c[ 0] ) * s[0];
    a <==  ( c[ 0] );

    out <==  (  a10 +  a1 +  a0 +  a );

}

template Mux2() {
    var i;
    signal input c[4];  // Constants
    signal input s[2];   // Selector
    signal output out;

    component mux = MultiMux2(1);

    for (i=0; i<4; i++) {
         mux.c[i] <== c[i];
    }

    for (i=0; i<2; i++) {
        s[i] ==> mux.s[i];
    }
    mux.out ==> out;
}
