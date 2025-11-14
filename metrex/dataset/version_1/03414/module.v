


module sky130_fd_sc_ms__nor2 (
    Y,
    A,
    B
);

    output Y;
    input  A;
    input  B;

    wire nor0_out_Y;

    nor nor0 (nor0_out_Y, A, B           );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
