


module sky130_fd_sc_lp__o2111ai (
    Y ,
    A1,
    A2,
    B1,
    C1,
    D1
);

    output Y ;
    input  A1;
    input  A2;
    input  B1;
    input  C1;
    input  D1;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire or0_out    ;
    wire nand0_out_Y;

    or   or0   (or0_out    , A2, A1             );
    nand nand0 (nand0_out_Y, C1, B1, D1, or0_out);
    buf  buf0  (Y          , nand0_out_Y        );

endmodule
