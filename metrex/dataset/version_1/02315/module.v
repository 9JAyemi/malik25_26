


module sky130_fd_sc_ms__o31ai (
    Y ,
    A1,
    A2,
    A3,
    B1
);

    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;

    wire or0_out    ;
    wire nand0_out_Y;

    or   or0   (or0_out    , A2, A1, A3     );
    nand nand0 (nand0_out_Y, B1, or0_out    );
    buf  buf0  (Y          , nand0_out_Y    );

endmodule
