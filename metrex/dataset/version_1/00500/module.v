


module sky130_fd_sc_hd__nor4bb (
    Y  ,
    A  ,
    B  ,
    C_N,
    D_N
);

    output Y  ;
    input  A  ;
    input  B  ;
    input  C_N;
    input  D_N;

    wire nor0_out  ;
    wire and0_out_Y;

    nor nor0 (nor0_out  , A, B              );
    and and0 (and0_out_Y, nor0_out, C_N, D_N);
    buf buf0 (Y         , and0_out_Y        );

endmodule
