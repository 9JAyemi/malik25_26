
module xor4 (
    X,
    A,
    B,
    C,
    D
);

    // Port declaration
    output X;
    input  A;
    input  B;
    input  C;
    input  D;

    // Internal signals
    wire AB, CD, ABCD;

    // Instantiate XOR gates
    xor (AB, A, B);
    xor (CD, C, D);
    xor (ABCD, AB, CD);

    // Output assignment
    assign X = ABCD;

endmodule
