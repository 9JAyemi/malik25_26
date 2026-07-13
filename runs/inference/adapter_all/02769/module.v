


module sky130_fd_sc_ms__a221oi (
    Y ,
    A1,
    A2,
    B1,
    B2,
    C1
);

    output Y ;
    input  A1;
    input  A2;
    input  B1;
    input  B2;
    input  C1;

    wire and0_out  ;
    wire and1_out  ;
    wire nor0_out_Y;

    and and0 (and0_out  , B1, B2                );
    and and1 (and1_out  , A1, A2                );
    nor nor0 (nor0_out_Y, and0_out, C1, and1_out);
    buf buf0 (Y         , nor0_out_Y            );

endmodule
