
module full_adder(A, B, Cin, S, Cout);

input A, B, Cin;
output S, Cout;

wire w1, w2, w3;

xor(w1, A, B);
xor(S, w1, Cin);
and(w2, A, B);
and(w3, w1, Cin);
or(Cout, w2, w3);

endmodule
module half_adder(A, B, S, Cout);

input A, B;
output S, Cout;

wire w1;

xor(S, A, B);
and(Cout, A, B);

endmodule
module four_bit_adder(A, B, Cin, S, Cout);

input [3:0] A, B;
input Cin;
output [3:0] S;
output Cout;

wire c1, c2, c3;

full_adder fa1(A[0], B[0], Cin, S[0], c1);
full_adder fa2(A[1], B[1], c1, S[1], c2);
full_adder fa3(A[2], B[2], c2, S[2], c3);
full_adder fa4(A[3], B[3], c3, S[3], Cout);

endmodule