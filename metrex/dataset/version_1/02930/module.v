module nand2 (
    input A,
    input B,
    output Y
);

    assign Y = ~(A & B);

endmodule

module nand4 (
    input A,
    input B,
    input C,
    input D,
    output Y,
    input VPB,
    input VPWR,
    input VGND,
    input VNB
);

    wire nand1_out, nand2_out, nand3_out, nand4_out;

    nand2 nand1 (
        .A(A),
        .B(B),
        .Y(nand1_out)
    );

    nand2 nand2 (
        .A(C),
        .B(D),
        .Y(nand2_out)
    );

    nand2 nand3 (
        .A(nand1_out),
        .B(nand2_out),
        .Y(nand3_out)
    );

    nand2 nand4 (
        .A(nand3_out),
        .B(nand3_out),
        .Y(Y)
    );

endmodule