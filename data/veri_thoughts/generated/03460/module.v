
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output Cout,
    output [3:0] S
);

    wire [2:0] carry;  // Internal carry wires

    // Full adder for bit 0
    xor(S[0], A[0], B[0], 0);   
    and(carry[0], A[0], B[0]);

    // Full adder for bit 1
    xor(S[1], A[1], B[1], carry[0]);
   
    majority maj0 (carry[1], A[1], B[1], carry[0]);

    // Full adder for bit 2
    xor(S[2], A[2], B[2], carry[1]);

    majority maj1 (carry[2], A[2], B[2], carry[1]);

    // Full adder for bit 3
    xor(S[3], A[3], B[3], carry[2]);
    majority maj2 (Cout, A[3], B[3], carry[2]);

endmodule
module majority(output out, input a, input b, input c);
    wire ab, bc, ac;
    and(ab, a, b);
    and(bc, b, c);
    and(ac, a, c);
    or(out, ab, bc, ac);
endmodule