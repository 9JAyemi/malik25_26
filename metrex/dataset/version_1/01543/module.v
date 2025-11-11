
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] Sum,
    output Cout
);

wire [3:0] carry;
wire [3:0] xor_sum;

// First bit
full_adder FA0(A[0], B[0], Cin, Sum[0], carry[0]);
assign xor_sum[0] = A[0] ^ B[0];

// Second bit
full_adder FA1(A[1], B[1], carry[0], Sum[1], carry[1]);
assign xor_sum[1] = A[1] ^ B[1];

// Third bit
full_adder FA2(A[2], B[2], carry[1], Sum[2], carry[2]);
assign xor_sum[2] = A[2] ^ B[2];

// Fourth bit
full_adder FA3(A[3], B[3], carry[2], Sum[3], carry[3]);
assign xor_sum[3] = A[3] ^ B[3];

assign Cout = carry[3] | xor_sum[3];

endmodule
module full_adder (
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);

wire sum1;
wire carry1;

// First adder
xor (sum1, A, B);
and (carry1, A, B);

// Second adder
xor (Sum, sum1, Cin);
and (Cout, sum1, Cin);

endmodule