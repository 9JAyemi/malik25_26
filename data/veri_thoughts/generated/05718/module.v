
module mux2to1 (
    output Y,
    input  A,
    input  B,
    input  S
);

    assign Y = S ? B : A;

endmodule
module mux4to1 (
    output Y,
    input  A,
    input  B,
    input  C,
    input  D,
    input  S0,
    input  S1
);

wire   m3_int;

mux2to1 m11 ( .Y(m3_int), .A(A), .B(B), .S(S0) );
mux2to1 m12 ( .Y(Y),       .A(C), .B(D), .S(S1) );

endmodule