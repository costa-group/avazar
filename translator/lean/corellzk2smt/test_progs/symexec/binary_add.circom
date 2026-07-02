template BinaryAdd(n){
    signal input a[n];
    signal input b[n];
    
    var cin = 0;
    var c = 0;
    var short_c = 0;
    
    signal output c_chunks[2*n];
    signal output cout[n];
    
    for(var i = 0; i<n;i++){
        c = a[i] + b[i] + cin;
        short_c = c & 4294967295;
        c_chunks[2*i] <-- short_c & 65535;
        c_chunks[2*i+1] <-- short_c >>16;
        
        if(c > 4294967295){
            cout[i] <-- 1;
            cin = 1;
        } else{
            cout[i] <-- 0;
            cin = 0;
        }
    }
}



component main = BinaryAdd(2);