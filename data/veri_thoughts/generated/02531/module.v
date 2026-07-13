module my_nand (
    input  A,
    input  B,
    output Y
);

    wire nand_out;
    assign nand_out = ~(A & B);

    nand_gate nand_gate_inst (
        .A_N(nand_out),
        .B(B),
        .Y(Y)
    );

endmodule

module nand_gate (
    input A_N,
    input B,
    output Y
);

    assign Y = ~(A_N & B);

endmodule