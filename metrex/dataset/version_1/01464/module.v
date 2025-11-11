
module sky130_fd_sc_hd__and2_1 (
    A,
    B,
    X
);

    input  A;
    input  B;
    output X;

    wire _TECHMAP_FAIL_ = A && B;

    assign X = _TECHMAP_FAIL_;

endmodule

module my_module (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    B2  ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  B2  ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    sky130_fd_sc_hd__and2_1 base (
        .A(A1),
        .B(A2),
        .X(Y)
    );

endmodule
