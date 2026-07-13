module binary_adder(
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] S,
    output C_out
);

wire [3:0] sum;
wire [3:0] carry_out;

full_adder fa0(A[0], B[0], C_in, sum[0], carry_out[0]);
full_adder fa1(A[1], B[1], carry_out[0], sum[1], carry_out[1]);
full_adder fa2(A[2], B[2], carry_out[1], sum[2], carry_out[2]);
full_adder fa3(A[3], B[3], carry_out[2], sum[3], C_out);

assign S = sum;

endmodule

module full_adder(
    input A,
    input B,
    input C_in,
    output S,
    output C_out
);

assign S = A ^ B ^ C_in;
assign C_out = (A & B) | (C_in & (A ^ B));

endmodule