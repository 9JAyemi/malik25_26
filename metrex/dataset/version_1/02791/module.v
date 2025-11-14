
module nand2 (
    input A,
    input B,
    output Y
);

    assign Y = ~(A & B);

endmodule
module and2 (
    input A,
    input B,
    output Y
);

    assign Y = A & B;

endmodule
module nand_gate (
    input A,
    input B,
    input VPWR,
    input VGND,
    input KAPWR,
    output Y
);

    wire nand_out;

    nand2 nand_gate_inst (
        .A(A),
        .B(B),
        .Y(nand_out)
    );

    and2 and_gate_inst (
        .A(nand_out),
        .B(KAPWR),
        .Y(Y)
    );

endmodule