
module my_module (
    output Y,
    input  A1,
    input  A2,
    input  A3,
    input  A4,
    input  B1,
    input  VPWR,
    input  VGND,
    input  VPB,
    input  VNB
);

    wire xor1, xor2;

    assign xor1 = A1 ^ A2;
    assign xor2 = A3 ^ A4;

    assign Y = (B1 & ~VPWR) ? xor1 : ((~B1) ? 0 : xor2);

endmodule
module sky130_fd_sc_lp__o41ai (
    output Y,
    input  A1,
    input  A2,
    input  A3,
    input  A4,
    input  B1,
    input  VPWR,
    input  VGND,
    input  VPB,
    input  VNB
);

endmodule