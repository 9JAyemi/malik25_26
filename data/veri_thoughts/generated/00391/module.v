module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

    wire [3:0] C;
    wire [3:0] G;
    wire [3:0] P;

    full_adder fa0 (A[0], B[0], Cin, S[0], C[0]);
    full_adder fa1 (A[1], B[1], C[0], S[1], C[1]);
    full_adder fa2 (A[2], B[2], C[1], S[2], C[2]);
    full_adder fa3 (A[3], B[3], C[2], S[3], Cout);

    assign G[0] = A[0] & B[0];
    assign G[1] = A[1] & B[1];
    assign G[2] = A[2] & B[2];
    assign G[3] = A[3] & B[3];

    assign P[0] = A[0] ^ B[0];
    assign P[1] = A[1] ^ B[1];
    assign P[2] = A[2] ^ B[2];
    assign P[3] = A[3] ^ B[3];

endmodule

module full_adder (
    input A,
    input B,
    input Cin,
    output S,
    output Cout
);

    wire C1;
    wire S1;
    wire S2;

    xor (S1, A, B);
    xor (S, S1, Cin);
    and (S2, S1, Cin);
    or (Cout, S2, A & B);

endmodule