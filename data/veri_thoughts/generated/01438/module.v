
module sky130_fd_sc_ls__nor4bb (
    output Y   ,
    input  A   ,
    input  B   ,
    input  C_N ,
    input  D_N ,
    input  VPWR,
    input  VGND,
    input  VPB ,
    input  VNB
);

    nor (Y, A, B, C_N, D_N);

endmodule
