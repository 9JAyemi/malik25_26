
module and3_not_A (
    input A,
    input B,
    input C,
    output X
);

    // Intermediate signals
    wire not_A, and_B_C;

    // Logic gates
    not not_A(not_A, A);
    and and_B_C(and_B_C, B, C);

    assign X = not_A & and_B_C;

endmodule
