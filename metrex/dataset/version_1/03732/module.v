


module sky130_fd_sc_hd__nand4b (
    Y  ,
    A_N,
    B  ,
    C  ,
    D
);

    output Y  ;
    input  A_N;
    input  B  ;
    input  C  ;
    input  D  ;

    wire not0_out   ;
    wire nand0_out_Y;

    not  not0  (not0_out   , A_N              );
    nand nand0 (nand0_out_Y, D, C, B, not0_out);
    buf  buf0  (Y          , nand0_out_Y      );

endmodule
