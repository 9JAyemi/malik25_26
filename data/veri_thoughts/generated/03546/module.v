module four_bit_adder (A, B, Cin, S, Cout);

  input [3:0] A, B;
  input Cin;
  output [3:0] S;
  output Cout;
  
  wire [3:0] C;
  
  // Instantiate full-adder modules
  full_adder FA0(.A(A[0]), .B(B[0]), .Cin(Cin), .S(S[0]), .Cout(C[0]));
  full_adder FA1(.A(A[1]), .B(B[1]), .Cin(C[0]), .S(S[1]), .Cout(C[1]));
  full_adder FA2(.A(A[2]), .B(B[2]), .Cin(C[1]), .S(S[2]), .Cout(C[2]));
  full_adder FA3(.A(A[3]), .B(B[3]), .Cin(C[2]), .S(S[3]), .Cout(Cout));
  
endmodule

module full_adder (A, B, Cin, S, Cout);

  input A, B, Cin;
  output S, Cout;
  
  assign S = A ^ B ^ Cin;
  assign Cout = (A & B) | (Cin & (A ^ B));
  
endmodule