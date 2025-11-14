


module sky130_fd_sc_ms__a21bo (
    X   ,
    A1  ,
    A2  ,
    B1_N
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1_N;

    wire nand0_out  ;
    wire nand1_out_X;

    nand nand0 (nand0_out  , A2, A1         );
    nand nand1 (nand1_out_X, B1_N, nand0_out);
    buf  buf0  (X          , nand1_out_X    );

endmodule
