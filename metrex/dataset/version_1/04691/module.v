
module adder4(
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output COUT
);

wire [4:0] sum;
wire carry;

assign {carry, sum} = A + B;
assign COUT = carry;

assign S = sum[3:0];

endmodule