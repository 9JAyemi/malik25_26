


module sky130_fd_sc_ms__xnor3 (
    X,
    A,
    B,
    C
);

    output X;
    input  A;
    input  B;
    input  C;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire xnor0_out_X;

    xnor xnor0 (xnor0_out_X, A, B, C        );
    buf  buf0  (X          , xnor0_out_X    );

endmodule
