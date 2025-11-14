


module sky130_fd_sc_ms__clkdlyinv5sd2 (
    Y,
    A
);

    output Y;
    input  A;

    wire not0_out_Y;

    not not0 (not0_out_Y, A              );
    buf buf0 (Y         , not0_out_Y     );

endmodule
