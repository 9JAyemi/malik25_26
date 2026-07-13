module mux_4_1_using_2_1 (A, B, C, D, S0, S1, Y);

input A, B, C, D, S0, S1;
output Y;

wire m1_out, m2_out;

// 2:1 Mux 1
mux_2_1 m1(.A(A), .B(B), .S(S0), .Y(m1_out));

// 2:1 Mux 2
mux_2_1 m2(.A(C), .B(D), .S(S0), .Y(m2_out));

// 2:1 Mux 3
mux_2_1 m3(.A(m1_out), .B(m2_out), .S(S1), .Y(Y));

endmodule

// 2:1 Mux Module
module mux_2_1 (A, B, S, Y);

input A, B, S;
output Y;

assign Y = (S == 1'b0) ? A : B;

endmodule