module nand3b (
    output Y,
    input A_N,
    input B,
    input C
);

    assign Y = ~(A_N & B & C);

endmodule

module nand4 (
    output Y,
    input A,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire nand1_out;
    wire nand2_out;
    wire nand3_out;

    nand3b nand1 (
        .Y(nand1_out),
        .A_N(A),
        .B(B),
        .C(VPB)
    );

    nand3b nand2 (
        .Y(nand2_out),
        .A_N(C),
        .B(D),
        .C(VPB)
    );

    nand3b nand3 (
        .Y(nand3_out),
        .A_N(nand1_out),
        .B(nand2_out),
        .C(VPB)
    );

    nand3b base (
        .Y(Y),
        .A_N(nand3_out),
        .B(VGND),
        .C(VPWR)
    );

endmodule