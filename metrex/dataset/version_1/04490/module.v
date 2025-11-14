


module sky130_fd_sc_lp__o21bai (
    Y   ,
    A1  ,
    A2  ,
    B1_N
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire b          ;
    wire or0_out    ;
    wire nand0_out_Y;

    not  not0  (b          , B1_N           );
    or   or0   (or0_out    , A2, A1         );
    nand nand0 (nand0_out_Y, b, or0_out     );
    buf  buf0  (Y          , nand0_out_Y    );

endmodule
