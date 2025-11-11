module xor_gate (
    A,
    B,
    X
);

    // Module ports
    input  A;
    input  B;
    output X;

    // Local signals
    wire xor_out;

    //  Name  Output      Other arguments
    xor xor0 (xor_out, A, B);

    //  Name  Output      Other arguments
    buf buf0 (X, xor_out);

endmodule