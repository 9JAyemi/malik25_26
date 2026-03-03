
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] S,
    output C_out
);

wire [3:0] sum;
wire [3:0] carry;

// Full adder for the least significant bit
full_adder fa0(A[0], B[0], C_in, sum[0], carry[0]);

// Full adder for the second least significant bit
full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);

// Full adder for the third least significant bit
full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);

// Full adder for the most significant bit
full_adder fa3(A[3], B[3], carry[2], sum[3], C_out);

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