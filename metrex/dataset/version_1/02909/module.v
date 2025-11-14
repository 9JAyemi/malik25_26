
module nor4 (
    A,
    B,
    C,
    D,
    Y
);

    input A, B, C, D;
    output Y;

    wire temp1, temp2;

    // First NOR gate
    nor_gate nor1 (
        .Y(temp1),
        .A(A),
        .B(B)
    );

    // Second NOR gate
    nor_gate nor2 (
        .Y(temp2),
        .A(C),
        .B(D)
    );

    // Final NOR gate
    nor_gate nor3 (
        .Y(Y),
        .A(temp1),
        .B(temp2)
    );

endmodule

module nor_gate (
    Y,
    A,
    B
);

    input A, B;
    output Y;

    assign Y = ~(A | B);

endmodule
