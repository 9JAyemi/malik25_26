module four_bit_adder (
  input [3:0] A,
  input [3:0] B,
  output [3:0] C,
  output overflow
);

  wire [3:0] sum;
  wire [3:0] carry;
  
  full_adder adder0 (A[0], B[0], 1'b0, sum[0], carry[0]);
  full_adder adder1 (A[1], B[1], carry[0], sum[1], carry[1]);
  full_adder adder2 (A[2], B[2], carry[1], sum[2], carry[2]);
  full_adder adder3 (A[3], B[3], carry[2], sum[3], overflow);
  
  assign C = sum;
  
endmodule

module full_adder (
  input A,
  input B,
  input Cin,
  output S,
  output Cout
);

  wire s1;
  wire c1;
  wire c2;
  
  xor (s1, A, B);
  xor (S, s1, Cin);
  and (c1, s1, Cin);
  and (c2, A, B);
  or (Cout, c1, c2);
  
endmodule