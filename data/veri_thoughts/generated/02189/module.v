module binary_adder (
  input [3:0] A,
  input [3:0] B,
  output [3:0] sum,
  output C_out
);

  wire [3:0] temp_sum;
  wire C1, C2, C3;

  // Full adder for bit 0
  full_adder FA0(A[0], B[0], 1'b0, temp_sum[0], C1);

  // Full adder for bit 1
  full_adder FA1(A[1], B[1], C1, temp_sum[1], C2);

  // Full adder for bit 2
  full_adder FA2(A[2], B[2], C2, temp_sum[2], C3);

  // Full adder for bit 3
  full_adder FA3(A[3], B[3], C3, temp_sum[3], C_out);

  assign sum = temp_sum;

endmodule

module full_adder (
  input A,
  input B,
  input C_in,
  output sum,
  output C_out
);

  assign sum = A ^ B ^ C_in;
  assign C_out = (A & B) | (C_in & (A ^ B));

endmodule