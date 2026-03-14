module and4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    // Local signals
    wire and0_out;
    wire and1_out;
    wire and2_out;

    // AND gates
    and and0 (and0_out, A, B);
    and and1 (and1_out, C, D);

    // 2-input AND gate
    and and2 (X, and0_out, and1_out);

endmodule