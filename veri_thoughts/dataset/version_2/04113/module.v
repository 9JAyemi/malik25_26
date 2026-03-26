


module sky130_fd_sc_ms__xor3 (
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

    wire xor0_out_X;

    xor xor0 (xor0_out_X, A, B, C        );
    buf buf0 (X         , xor0_out_X     );

endmodule
