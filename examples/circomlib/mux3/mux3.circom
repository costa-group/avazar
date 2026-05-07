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

template MultiMux3(n) {
    signal input c[8];  // Constants
    signal input s[3];   // Selector
    signal output out;

    signal a210;
    signal a21;
    signal a20;
    signal a2;

    signal a10;
    signal a1;
    signal a0;
    signal a;

    // 4 constrains for the intermediary variables
    signal  s10;
    s10 <== s[1] * s[0];

         a210 <==  ( c[ 7]-c[ 6]-c[ 5]+c[ 4] - c[ 3]+c[ 2]+c[ 1]-c[ 0] ) * s10;
          a21 <==  ( c[ 6]-c[ 4]-c[ 2]+c[ 0] ) * s[1];
          a20 <==  ( c[ 5]-c[ 4]-c[ 1]+c[ 0] ) * s[0];
           a2 <==  ( c[ 4]-c[ 0] );

          a10 <==  ( c[ 3]-c[ 2]-c[ 1]+c[ 0] ) * s10;
           a1 <==  ( c[ 2]-c[ 0] ) * s[1];
           a0 <==  ( c[ 1]-c[ 0] ) * s[0];
            a <==  ( c[ 0] );

          out <== ( a210 + a21 + a20 + a2 ) * s[2] +
                     (  a10 +  a1 +  a0 +  a );

}

template Mux3() {
    var i;
    signal input c[8];  // Constants
    signal input s[3];   // Selector
    signal output out;

    component mux = MultiMux3(1);

    for (i=0; i<8; i++) {
        mux.c[i] <== c[i];
    }

    for (i=0; i<3; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out ==> out;
}
