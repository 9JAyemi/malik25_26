
module mux4_2(
    input A,
    input B,
    input C,
    input D,
    input [1:0] S,
    output Y
);

wire w1, w2;

mux2 m0(.A(A), .B(B), .S(S[0]), .Y(w1));
mux2 m1(.A(C), .B(D), .S(S[0]), .Y(w2));
mux2 m2(.A(w1), .B(w2), .S(S[1]), .Y(Y));

endmodule

module mux2(
    input A,
    input B,
    input S,
    output Y
);

assign Y = (~S & A) | (S & B);

endmodule
