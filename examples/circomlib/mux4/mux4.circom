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

template MultiMux4(n) {
    signal input c[16];  // Constants
    signal input s[4];   // Selector
    signal output out;

    signal a3210;
    signal a321;
    signal a320;
    signal a310;
    signal a32;
    signal a31;
    signal a30;
    signal a3;

    signal a210;
    signal a21;
    signal a20;
    signal a10;
    signal a2;
    signal a1;
    signal a0;
    signal a;

    // 4 constrains for the intermediary variables
    signal  s10;
    s10 <== s[1] * s[0];
    signal  s20;
    s20 <== s[2] * s[0];
    signal  s21;
    s21 <== s[2] * s[1];
    signal s210;
    s210 <==  s21 * s[0];


        a3210 <==  ( c[15]-c[14]-c[13]+c[12] - c[11]+c[10]+c[ 9]-c[ 8]
                       -c[ 7]+c[ 6]+c[ 5]-c[ 4] + c[ 3]-c[ 2]-c[ 1]+c[ 0] ) * s210;
         a321 <==  ( c[14]-c[12]-c[10]+c[ 8] - c[ 6]+c[ 4]+c[ 2]-c[ 0] ) * s21;
         a320 <==  ( c[13]-c[12]-c[ 9]+c[ 8] - c[ 5]+c[ 4]+c[ 1]-c[ 0] ) * s20;
         a310 <==  ( c[11]-c[10]-c[ 9]+c[ 8] - c[ 3]+c[ 2]+c[ 1]-c[ 0] ) * s10;
          a32 <==  ( c[12]-c[ 8]-c[ 4]+c[ 0] ) * s[2];
          a31 <==  ( c[10]-c[ 8]-c[ 2]+c[ 0] ) * s[1];
          a30 <==  ( c[ 9]-c[ 8]-c[ 1]+c[ 0] ) * s[0];
           a3 <==  ( c[ 8]-c[ 0] );

         a210 <==  ( c[ 7]-c[ 6]-c[ 5]+c[ 4] - c[ 3]+c[ 2]+c[ 1]-c[ 0] ) * s210;
          a21 <==  ( c[ 6]-c[ 4]-c[ 2]+c[ 0] ) * s21;
          a20 <==  ( c[ 5]-c[ 4]-c[ 1]+c[ 0] ) * s20;
          a10 <==  ( c[ 3]-c[ 2]-c[ 1]+c[ 0] ) * s10;
           a2 <==  ( c[ 4]-c[ 0] ) * s[2];
           a1 <==  ( c[ 2]-c[ 0] ) * s[1];
           a0 <==  ( c[ 1]-c[ 0] ) * s[0];
            a <==  ( c[ 0] );

          out <== ( a3210 + a321 + a320 + a310 + a32 + a31 + a30 + a3 ) * s[3] +
                     (  a210 +  a21 +  a20 +  a10 +  a2 +  a1 +  a0 +  a );

/*
        out <== (  s210 * ( c[15]-c[14]-c[13]+c[12] - c[11]+c[10]+c[ 9]-c[ 8]
                              -c[ 7]+c[ 6]+c[ 5]-c[ 4] + c[ 3]-c[ 2]-c[ 1]+c[ 0] ) +
                       s21 * ( c[14]-c[12]-c[10]+c[ 8] - c[ 6]+c[ 4]+c[ 2]-c[ 0] ) +
                       s20 * ( c[13]-c[12]-c[ 9]+c[ 8] - c[ 5]+c[ 4]+c[ 1]-c[ 0] ) +
                       s10 * ( c[11]-c[10]-c[ 9]+c[ 8] - c[ 3]+c[ 2]+c[ 1]-c[ 0] ) +
                      s[2] * ( c[12]-c[ 8]-c[ 4]+c[ 0] ) +
                      s[1] * ( c[10]-c[ 8]-c[ 2]+c[ 0] ) +
                      s[0] * ( c[ 9]-c[ 8]-c[ 1]+c[ 0] ) +
                             ( c[ 8]-c[ 0] ) ) * s[3]  +
                (     s210 * ( c[ 7]-c[ 6]-c[ 5]+c[ 4] - c[ 3]+c[ 2]+c[ 1]-c[ 0] ) +
                       s21 * ( c[ 6]-c[ 4]-c[ 2]+c[ 0] ) +
                       s20 * ( c[ 5]-c[ 4]-c[ 1]+c[ 0] ) +
                       s10 * ( c[ 3]-c[ 2]-c[ 1]+c[ 0] ) +
                      s[2] * ( c[ 4]-c[ 0] ) +
                      s[1] * ( c[ 2]-c[ 0] ) +
                      s[0] * ( c[ 1]-c[ 0] ) +
                             ( c[ 0] ));

*/
}

template Mux4() {
    var i;
    signal input c[16];  // Constants
    signal input s[4];   // Selector
    signal output out;

    component mux = MultiMux4(1);

    for (i=0; i<16; i++) {
        mux.c[i] <== c[i];
    }

    for (i=0; i<4; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out ==> out;
}
