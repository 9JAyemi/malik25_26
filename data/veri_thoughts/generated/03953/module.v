module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input C_in,
    output [3:0] S,
    output C_out
);

wire [3:0] sum;
wire [3:0] carry;

full_adder FA0(.A(A[0]), .B(B[0]), .C_in(C_in), .S(sum[0]), .C_out(carry[0]));
full_adder FA1(.A(A[1]), .B(B[1]), .C_in(carry[0]), .S(sum[1]), .C_out(carry[1]));
full_adder FA2(.A(A[2]), .B(B[2]), .C_in(carry[1]), .S(sum[2]), .C_out(carry[2]));
full_adder FA3(.A(A[3]), .B(B[3]), .C_in(carry[2]), .S(sum[3]), .C_out(C_out));

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