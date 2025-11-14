
module adder(input [3:0] A, input [3:0] B, input Cin, output [3:0] S, output Cout);

  wire C1, C2, C3;
  wire S0, S1, S2, S3;
  
  // 1st bit
  full_adder FA1(A[0], B[0], Cin, S0, C1);
  
  // 2nd bit
  full_adder FA2(A[1], B[1], C1, S1, C2);
  
  // 3rd bit
  full_adder FA3(A[2], B[2], C2, S2, C3);
  
  // 4th bit
  full_adder FA4(A[3], B[3], C3, S3, Cout);
  
  assign S = {S3, S2, S1, S0};
  
endmodule
module full_adder(input A, input B, input Cin, output S, output Cout);
  
  wire X, Y, G, P;
  
  // First stage
  xor (X, A, B);
  and (Y, A, B);
  
  // Second stage
  xor (S, X, Cin);
  and (G, X, Cin);
  
  // Third stage
  and (P, Y, Cin);
  or (Cout, G, P);
  
endmodule