


module sky130_fd_sc_lp__o41ai (
    Y ,
    A1,
    A2,
    A3,
    A4,
    B1
);

    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  A4;
    input  B1;

    wire or0_out    ;
    wire nand0_out_Y;

    or   or0   (or0_out    , A4, A3, A2, A1 );
    nand nand0 (nand0_out_Y, B1, or0_out    );
    buf  buf0  (Y          , nand0_out_Y    );

endmodule
