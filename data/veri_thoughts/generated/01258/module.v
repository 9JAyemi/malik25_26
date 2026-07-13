


module sky130_fd_sc_lp__nand4 (
    Y,
    A,
    B,
    C,
    D
);

    output Y;
    input  A;
    input  B;
    input  C;
    input  D;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nand0_out_Y;

    nand nand0 (nand0_out_Y, D, C, B, A     );
    buf  buf0  (Y          , nand0_out_Y    );

endmodule
