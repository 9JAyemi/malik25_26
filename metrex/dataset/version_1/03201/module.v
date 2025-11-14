module nor4b (
    Y  ,
    Y_N,
    A  ,
    B  ,
    C  ,
    D_N
);

    // Module ports
    output Y  ;
    output Y_N;
    input  A  ;
    input  B  ;
    input  C  ;
    input  D_N;

    // Local signals
    wire not0_out  ;
    wire nor0_out_Y;

    // Implement NOT gate using built-in "not" primitive
    not not0 (not0_out, D_N);

    // Implement NOR gate using built-in "nor" primitive
    nor nor0 (nor0_out_Y, A, B, C, not0_out);

    // Implement buffer to invert output of NOR gate
    buf buf0 (Y, nor0_out_Y);
    not not1 (Y_N, Y);

endmodule