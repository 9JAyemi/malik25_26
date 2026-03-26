
module sky130_fd_sc_lp__a21bo_lp (
    X   ,
    A1  ,
    A2  ,
    B1_N,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output X   ;
    input  A1  ;
    input  A2  ;
    input  B1_N;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    wire B1;

    nand (B1, A1, A2);

    not (X, B1);

    not (B1, B1_N);

endmodule