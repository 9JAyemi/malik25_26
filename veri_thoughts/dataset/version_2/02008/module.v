
module nor4 (
    Y  ,
    A  ,
    B  ,
    C_N,
    D_N
);

    output Y  ;
    input  A  ;
    input  B  ;
    input  C_N;
    input  D_N;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire A_N;
    wire B_N;
    wire C_N_N;
    wire D_N_N;
    wire Y;

    not n1(A_N, A);
    not n2(B_N, B);
    not n3(C_N_N, C_N);
    not n4(D_N_N, D_N);

    nand (Y, A_N, B_N, C_N_N, D_N_N);

endmodule