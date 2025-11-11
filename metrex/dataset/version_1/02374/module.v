


module sky130_fd_sc_ls__xor2 (
    X,
    A,
    B
);

    output X;
    input  A;
    input  B;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire xor0_out_X;

    xor xor0 (xor0_out_X, B, A           );
    buf buf0 (X         , xor0_out_X     );

endmodule
