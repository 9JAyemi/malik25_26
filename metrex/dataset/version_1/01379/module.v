
module sky130_fd_sc_h__a2bb2o_1 (
    X   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    output X   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Implement AND gate functionality
    assign X = (A1_N & A2_N) | (B1 & B2);

endmodule

module my_AND_gate (
    X   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    output X   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    // Instantiate sky130_fd_sc_h__a2bb2o_1 module
    sky130_fd_sc_h__a2bb2o_1 AND_gate (
        .X(X),
        .A1_N(A1_N),
        .A2_N(A2_N),
        .B1(B1),
        .B2(B2)
    );

endmodule
