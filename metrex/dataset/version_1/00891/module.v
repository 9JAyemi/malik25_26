
module add4(
    input [3:0] A,
    input [3:0] B,
    output [4:0] C
);

wire [3:0] sum;
wire carry_out;

assign {carry_out, sum} = A + B;

assign C[0] = sum[0];
assign C[1] = sum[1];
assign C[2] = sum[2];
assign C[3] = sum[3];
assign C[4] = carry_out;

endmodule