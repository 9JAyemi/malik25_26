


module sky130_fd_sc_lp__or4bb (
    X  ,
    A  ,
    B  ,
    C_N,
    D_N
);

    output X  ;
    input  A  ;
    input  B  ;
    input  C_N;
    input  D_N;

    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire nand0_out;
    wire or0_out_X;

    nand nand0 (nand0_out, D_N, C_N       );
    or   or0   (or0_out_X, B, A, nand0_out);
    buf  buf0  (X        , or0_out_X      );

endmodule
