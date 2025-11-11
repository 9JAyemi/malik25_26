


module sky130_fd_sc_ls__nor4 (
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

    wire nor0_out_Y;

    nor nor0 (nor0_out_Y, A, B, C, D     );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
