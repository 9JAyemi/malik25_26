


module sky130_fd_sc_lp__a21oi (
    Y ,
    A1,
    A2,
    B1
);

    output Y ;
    input  A1;
    input  A2;
    input  B1;

    wire and0_out  ;
    wire nor0_out_Y;

    and and0 (and0_out  , A1, A2         );
    nor nor0 (nor0_out_Y, B1, and0_out   );
    buf buf0 (Y         , nor0_out_Y     );

endmodule
