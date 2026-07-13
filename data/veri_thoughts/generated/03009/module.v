module nand4(
    input A,
    input B,
    input C,
    input D,
    output Y,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire nand1_out, nand2_out, nand3_out;
    nand4bb_4 nand1(
        .Y(nand1_out),
        .A_N(A),
        .B_N(B),
        .C_N(C),
        .D_N(D),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    nand4bb_4 nand2(
        .Y(nand2_out),
        .A_N(nand1_out),
        .B_N(nand1_out),
        .C_N(nand1_out),
        .D_N(nand1_out),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    nand4bb_4 nand3(
        .Y(nand3_out),
        .A_N(nand2_out),
        .B_N(nand2_out),
        .C_N(nand2_out),
        .D_N(nand2_out),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    nand4bb_4 nand4(
        .Y(Y),
        .A_N(nand3_out),
        .B_N(nand3_out),
        .C_N(nand3_out),
        .D_N(nand3_out),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule

module nand4bb_4(
    output Y,
    input A_N,
    input B_N,
    input C_N,
    input D_N,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    // NAND gate functionality
    assign Y = ~(A_N & B_N & C_N & D_N);

endmodule