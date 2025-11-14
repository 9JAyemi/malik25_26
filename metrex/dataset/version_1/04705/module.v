module MUX4to1 (A, B, C, D, S, Y);
input A, B, C, D;
input [1:0] S;
output Y;

wire sel0, sel1;

// Decode select input
assign sel0 = ~S[0];
assign sel1 = ~S[1];

// Generate output
assign Y = (sel1 & sel0 & A) | (sel1 & ~sel0 & B) | (~sel1 & sel0 & C) | (~sel1 & ~sel0 & D);

endmodule