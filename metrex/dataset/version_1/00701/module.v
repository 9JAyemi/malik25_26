
module mux21 (
    input A,
    input B,
    input S,
    output Y
);

  assign Y = (~S & A) | (S & B);

endmodule
module demux (
    input in0, in1, in2, in3, d0, d1,
    output out
);

  wire n1, n2;

  mux21 U0 ( .A(n1), .B(n2), .S(d1), .Y(out) );
  mux21 U1 ( .A(in2), .B(in3), .S(d0), .Y(n2) );
  mux21 U2 ( .A(in0), .B(in1), .S(d0), .Y(n1) );

endmodule
module mux41 (
    input A0, A1, A2, A3,
    input B0, B1, B2, B3,
    input S0, S1,
    output Y
);

  wire n1, n2;

  mux21 U0 ( .A(A0), .B(A1), .S(S0), .Y(n1) );
  mux21 U1 ( .A(A2), .B(A3), .S(S0), .Y(n2) );
  mux21 U2 ( .A(n1), .B(n2), .S(S1), .Y(Y) );

endmodule