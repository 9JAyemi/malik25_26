module sky130_fd_sc_lp__invlp (
    input  A   ,
    output Y   ,
    input  VPB ,
    input  VPWR,
    input  VGND,
    input  VNB
);

assign Y = ~A;

endmodule