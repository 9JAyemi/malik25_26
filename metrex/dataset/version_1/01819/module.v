
module full_adder(output sum, carry_out, input a, b, carry_in);
    wire w1, w2, w3;
    xor(sum, a, b, carry_in);
    and(w1, a, b);
    and(w2, a, carry_in);
    and(w3, b, carry_in);
    or(carry_out, w1, w2, w3);
endmodule
module ripple_carry_adder(output [3:0] S, output Cout, input [3:0] A, B, input Cin);
    wire [2:0] c;
    full_adder fa1(S[0], c[0], A[0], B[0], Cin);
    full_adder fa2(S[1], c[1], A[1], B[1], c[0]);
    full_adder fa3(S[2], c[2], A[2], B[2], c[1]);
    full_adder fa4(S[3], Cout, A[3], B[3], c[2]);
endmodule