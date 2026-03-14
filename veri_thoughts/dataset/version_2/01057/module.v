
module four_bit_adder(
  input [3:0] A,
  input [3:0] B,
  output [3:0] S,
  output C
);

  wire [3:0] sum;
  wire C1, C2, C3; // Intermediate carry signals

  // Full adder for least significant bit
  full_adder fa0(
    .a(A[0]),
    .b(B[0]),
    .c_in(1'b0),
    .sum(sum[0]),
    .c_out(C1)
  );
  
  // Full adder for second least significant bit
  full_adder fa1(
    .a(A[1]),
    .b(B[1]),
    .c_in(C1),
    .sum(sum[1]),
    .c_out(C2)
  );
  
  // Full adder for third least significant bit
  full_adder fa2(
    .a(A[2]),
    .b(B[2]),
    .c_in(C2),
    .sum(sum[2]),
    .c_out(C3)
  );
  
  // Full adder for most significant bit
  full_adder fa3(
    .a(A[3]),
    .b(B[3]),
    .c_in(C3),
    .sum(sum[3]),
    .c_out(C)
  );
  
  assign S = sum;
  
endmodule
module full_adder(
  input a,
  input b,
  input c_in,
  output sum,
  output c_out
);

  assign sum = a ^ b ^ c_in;
  assign c_out = (a & b) | (a & c_in) | (b & c_in);
  
endmodule