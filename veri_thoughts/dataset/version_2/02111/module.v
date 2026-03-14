
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S
);

    wire [3:0] C; // Carry

    // First bit
    xor xor1(S[0], A[0], B[0]);
    and and1(C[0], A[0], B[0]);

    // Second bit
    xor xor2(S[1], A[1], B[1]);
    and and2(C[1], A[1], B[1]);
    or or1(C[1], C[1], C[0]);

    // Third bit
    xor xor3(S[2], A[2], B[2]);
    and and3(C[2], A[2], B[2]);
    or or2(C[2], C[2], C[1]);

    // Fourth bit
    xor xor4(S[3], A[3], B[3]);
    and and4(C[3], A[3], B[3]);
    or or3(C[3], C[3], C[2]);

endmodule