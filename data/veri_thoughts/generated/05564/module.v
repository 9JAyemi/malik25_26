module four_bit_adder(A, B, C_in, S, C_out);

input [3:0] A, B;
input C_in;
output [3:0] S;
output C_out;

wire [3:0] sum;
wire [3:0] carry;

// First full adder
full_adder FA0(A[0], B[0], C_in, sum[0], carry[0]);

// Second full adder
full_adder FA1(A[1], B[1], carry[0], sum[1], carry[1]);

// Third full adder
full_adder FA2(A[2], B[2], carry[1], sum[2], carry[2]);

// Fourth full adder
full_adder FA3(A[3], B[3], carry[2], sum[3], C_out);

assign S = sum;

endmodule

module full_adder(A, B, C_in, S, C_out);

input A, B, C_in;
output S, C_out;

wire s1, s2, c1, c2;

// First half adder
half_adder HA1(A, B, s1, c1);

// Second half adder
half_adder HA2(s1, C_in, S, c2);

// Carry out
assign C_out = c1 | c2;

endmodule

module half_adder(A, B, S, C_out);

input A, B;
output S, C_out;

assign S = A ^ B;
assign C_out = A & B;

endmodule