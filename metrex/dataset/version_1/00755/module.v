module mux2to1 (
    input  I0,
    input  I1,
    input  S,
    output Y
);

assign Y = (S) ? I1 : I0;

endmodule

module mux4to1 (
    input  A,
    input  B,
    input  C,
    input  D,
    input  S0,
    input  S1,
    output Y
);

wire w1, w2, w3;

mux2to1 m1 (.I0(A), .I1(B), .S(S1), .Y(w1));
mux2to1 m2 (.I0(C), .I1(D), .S(S1), .Y(w2));
mux2to1 m3 (.I0(w1), .I1(w2), .S(S0), .Y(w3));
assign Y = w3;

endmodule