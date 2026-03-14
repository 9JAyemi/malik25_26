
module or4_module (
    X  ,
    A  ,
    B  ,
    C_N,
    D_N
);

    output X  ;
    input  A  ;
    input  B  ;
    input  C_N;
    input  D_N;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    assign X = A | B | ~C_N | ~D_N;

endmodule
