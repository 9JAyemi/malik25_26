


module sky130_fd_sc_hd__nor4 (
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

    wire nor0_out_Y;

    nor nor0 (nor0_out_Y, A, B, C, D     );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
