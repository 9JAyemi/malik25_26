module four_input_and (
    A1,
    A2,
    B1_N,
    C1,
    X
);

    input A1;
    input A2;
    input B1_N;
    input C1;
    output X;

    wire and1_out;
    wire and2_out;

    o21ba and1 (
        .A1(A1),
        .A2(A2),
        .B1_N(B1_N),
        .X(and1_out)
    );

    o21ba and2 (
        .A1(A1),
        .A2(A2),
        .B1_N(C1),
        .X(and2_out)
    );

    assign X = and1_out & and2_out;

endmodule

module o21ba (
    input A1,
    input A2,
    input B1_N,
    output X
);

    // Implementing the logic: X = A1 & A2 & ~B1_N
    assign X = A1 & A2 & ~B1_N;

endmodule
