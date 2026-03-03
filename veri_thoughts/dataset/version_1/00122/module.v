
module Mult4x4
(
 input wire [3:0] A,
 input wire [3:0] B,
 output wire [7:0] Result
);

wire [5:0] wResInt1,wResInt2;

assign wResInt1 = A * B[1:0];
assign wResInt2 = A * B[3:2];

assign Result = ((wResInt2<<2) + wResInt1);

endmodule
