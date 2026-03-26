


module sky130_fd_sc_ms__o2bb2ai (
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

    wire nand0_out  ;
    wire or0_out    ;
    wire nand1_out_Y;

    nand nand0 (nand0_out  , A2_N, A1_N        );
    or   or0   (or0_out    , B2, B1            );
    nand nand1 (nand1_out_Y, nand0_out, or0_out);
    buf  buf0  (Y          , nand1_out_Y       );

endmodule
