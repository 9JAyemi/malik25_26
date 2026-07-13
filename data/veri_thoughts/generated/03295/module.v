
module binary_adder(A, B, S, CO);
input A;
input B;
output S;
output CO;

wire w1, w2;
xor x1(w1, A, B);
and a1(w2, A, B);
xor x2(S, w1, CO);
and a2(CO, w2, w1);

endmodule