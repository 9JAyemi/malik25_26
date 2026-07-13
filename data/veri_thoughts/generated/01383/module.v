
module four_bit_adder(
  input [3:0] A,
  input [3:0] B,
  input Cin,
  output Cout,
  output [3:0] S
);

  wire [3:0] temp_sum;
  wire C0, C1, C2;
  
  // Full adder for the least significant bit
  full_adder FA0(A[0], B[0], Cin, temp_sum[0], C0);
  
  // Full adder for the second least significant bit
  full_adder FA1(A[1], B[1], C0, temp_sum[1], C1);
  
  // Full adder for the third least significant bit
  full_adder FA2(A[2], B[2], C1, temp_sum[2], C2);
  
  // Full adder for the most significant bit
  full_adder FA3(A[3], B[3], C2, temp_sum[3], Cout);
  
  assign S = temp_sum;
  
endmodule
module full_adder(
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (Cin & (A ^ B));
  
endmodule