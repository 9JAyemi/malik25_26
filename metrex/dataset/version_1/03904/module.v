module sky130_fd_sc_lp__a2bb2oi (
    Y   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    output Y   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    assign Y = (A1_N & B1) | (A2_N & B2);

endmodule

module sky130_fd_sc_lp__a2bb2oi_lp (
    Y   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    output Y   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    sky130_fd_sc_lp__a2bb2oi base (
        .Y(Y),
        .A1_N(A1_N),
        .A2_N(A2_N),
        .B1(B1),
        .B2(B2)
    );

endmodule