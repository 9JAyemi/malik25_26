
module nand_gate (
    input A,
    input B,
    output X
);

    assign X = ~(A & B);

endmodule
module or_gate (
    input A,
    input B,
    output X
);

    assign X = A | B;

endmodule
module not_gate (
    input A,
    output X
);

    assign X = ~A;

endmodule
module nand_or (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire nand1;
    wire nand2;
    wire or1;

    nand_gate nand_gate1 (
        .A(A),
        .B(B),
        .X(nand1)
    );

    nand_gate nand_gate2 (
        .A(nand1),
        .B(C),
        .X(nand2)
    );

    or_gate or_gate1 (
        .A(A),
        .B(B),
        .X(or1)
    );

    nand_gate nand_gate3 (
        .A(or1),
        .B(nand2),
        .X(X)
    );

endmodule