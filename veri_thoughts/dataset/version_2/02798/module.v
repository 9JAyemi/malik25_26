module sky130_fd_sc_ls__o22a (
    output X,
    input  A1,
    input  A2,
    input  B1,
    input  B2,
    input  VPWR,
    input  VGND,
    input  VPB,
    input  VNB
);

    assign X = A1 & A2 | B1 & B2 | VPWR | VGND | VPB | VNB;

endmodule