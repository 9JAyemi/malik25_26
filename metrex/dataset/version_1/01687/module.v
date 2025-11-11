
module inverter_gate (
    input  A,
    output Z,
    input  TE,
    input  VPB,
    input  VPWR,
    input  VGND,
    input  VNB
);

    wire inv_A;

    assign inv_A = ~A;

    assign Z = (TE) ? inv_A : VNB;

endmodule