
module four_bit_adder (A, B, Cin, Sum, Cout);
  input [3:0] A, B;
  input Cin;
  output [3:0] Sum;
  output Cout;

  wire [3:0] temp_sum;

  // First bit
  assign temp_sum[0] = A[0] ^ B[0] ^ Cin;

  // Second bit
  assign temp_sum[1] = A[1] ^ B[1] ^ temp_sum[0];

  // Third bit
  assign temp_sum[2] = A[2] ^ B[2] ^ temp_sum[1];

  // Fourth bit
  assign temp_sum[3] = A[3] ^ B[3] ^ temp_sum[2];

  assign Sum = temp_sum;

  assign Cout = temp_sum[3];

endmodule