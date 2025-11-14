


module sky130_fd_sc_lp__o221ai (
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

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire or0_out    ;
    wire or1_out    ;
    wire nand0_out_Y;

    or   or0   (or0_out    , B2, B1              );
    or   or1   (or1_out    , A2, A1              );
    nand nand0 (nand0_out_Y, or1_out, or0_out, C1);
    buf  buf0  (Y          , nand0_out_Y         );

endmodule
