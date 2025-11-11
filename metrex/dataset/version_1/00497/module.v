


module sky130_fd_sc_ls__nand4bb (
    Y  ,
    A_N,
    B_N,
    C  ,
    D
);

    output Y  ;
    input  A_N;
    input  B_N;
    input  C  ;
    input  D  ;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nand0_out;
    wire or0_out_Y;

    nand nand0 (nand0_out, D, C               );
    or   or0   (or0_out_Y, B_N, A_N, nand0_out);
    buf  buf0  (Y        , or0_out_Y          );

endmodule
