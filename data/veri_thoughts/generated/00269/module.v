


module sky130_fd_sc_ls__a2bb2oi (
    Y   ,
    A1_N,
    A2_N,
    B1  ,
    B2
);

    output Y   ;
    input  A1_N;
    input  A2_N;
    input  B1  ;
    input  B2  ;

    wire and0_out  ;
    wire nor0_out  ;
    wire nor1_out_Y;

    and and0 (and0_out  , B1, B2            );
    nor nor0 (nor0_out  , A1_N, A2_N        );
    nor nor1 (nor1_out_Y, nor0_out, and0_out);
    buf buf0 (Y         , nor1_out_Y        );

endmodule
