module mux2to1 (A, B, S, Y);
input A, B, S;
output Y;

wire Y_int;

assign Y = (S == 1'b0) ? A : B;

endmodule