module and_gate (
    input A,
    input B,
    output X
);

    wire not_A, not_B, and_AB;

    // Invert A and B
    inv_1 inv_A (
        .A(A),
        .X(not_A)
    );

    inv_1 inv_B (
        .A(B),
        .X(not_B)
    );

    // AND the inverted signals
    and2 and_inv (
        .A(not_A),
        .B(not_B),
        .X(and_AB)
    );

    // Invert the AND output
    inv_1 inv_AB (
        .A(and_AB),
        .X(X)
    );

endmodule

module inv_1 (
    input A,
    output X
);

    assign X = ~A;

endmodule

module and2 (
    input A,
    input B,
    output X
);

    assign X = A & B;

endmodule