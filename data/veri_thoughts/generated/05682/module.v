


module sky130_fd_sc_hd__nor2 (
    Y,
    A,
    B
);

    output Y;
    input  A;
    input  B;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nor0_out_Y;

    nor nor0 (nor0_out_Y, A, B           );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
