module nand2 (
    input a,
    input b,
    output y
);

    assign y = ~(a & b);

endmodule

module nand4 (
    input A,
    input B,
    input C,
    input D,
    output Y
);

    wire AB;
    wire CD;

    nand2 U1 (
        .a(A),
        .b(B),
        .y(AB)
    );

    nand2 U2 (
        .a(C),
        .b(D),
        .y(CD)
    );

    nand2 U3 (
        .a(AB),
        .b(CD),
        .y(Y)
    );

endmodule