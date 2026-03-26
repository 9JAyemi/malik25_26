
module MUX_4_1 (A, B, S, Y);
input A, B, S;
output Y;

wire Y1, Y2;
bufif1 buf1(Y1, A, ~S);
bufif1 buf2(Y2, B, S);
mux2to1 mux2to1_inst(.A(Y1), .B(Y2), .S(S), .Y(Y));

endmodule

module mux2to1 (A, B, S, Y);
input A, B, S;
output Y;

assign Y = S ? B : A;

endmodule
