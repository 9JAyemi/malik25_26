


module sky130_fd_sc_ms__nor3b (
    Y  ,
    A  ,
    B  ,
    C_N
);

    output Y  ;
    input  A  ;
    input  B  ;
    input  C_N;

    wire nor0_out  ;
    wire and0_out_Y;

    nor nor0 (nor0_out  , A, B           );
    and and0 (and0_out_Y, C_N, nor0_out  );
    buf buf0 (Y         , and0_out_Y     );

endmodule
