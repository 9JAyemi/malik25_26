
module full_adder (
  input A,
  input B,
  input cin,
  output sum,
  output cout
);

assign sum = A ^ B ^ cin;
assign cout = (A & B) | (cin & (A ^ B));

endmodule
module binary_multiplier (
  input [3:0] A,
  input [3:0] B,
  output [7:0] P
);

wire [3:0] S0, S1, S2, S3;
wire [3:0] C0, C1, C2, C3;

full_adder fa0(A[0], B[0], 1'b0, S0[0], C0[0]);
full_adder fa1(A[1], B[0], C0[0], S0[1], C0[1]);
full_adder fa2(A[2], B[0], C0[1], S0[2], C0[2]);
full_adder fa3(A[3], B[0], C0[2], S0[3], C0[3]);

full_adder fa4(A[0], B[1], 1'b0, S1[0], C1[0]);
full_adder fa5(A[1], B[1], C1[0], S1[1], C1[1]);
full_adder fa6(A[2], B[1], C1[1], S1[2], C1[2]);
full_adder fa7(A[3], B[1], C1[2], S1[3], C1[3]);

full_adder fa8(A[0], B[2], 1'b0, S2[0], C2[0]);
full_adder fa9(A[1], B[2], C2[0], S2[1], C2[1]);
full_adder fa10(A[2], B[2], C2[1], S2[2], C2[2]);
full_adder fa11(A[3], B[2], C2[2], S2[3], C2[3]);

full_adder fa12(A[0], B[3], 1'b0, S3[0], C3[0]);
full_adder fa13(A[1], B[3], C3[0], S3[1], C3[1]);
full_adder fa14(A[2], B[3], C3[1], S3[2], C3[2]);
full_adder fa15(A[3], B[3], C3[2], S3[3], C3[3]);

assign P = {C3[3], C3[2], C3[1], C3[0], S3, S2, S1, S0};

endmodule