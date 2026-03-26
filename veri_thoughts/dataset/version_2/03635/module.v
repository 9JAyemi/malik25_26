module ripple_carry_adder (A, B, Cin, S, Cout);
  input [3:0] A, B;
  input Cin;
  output [3:0] S;
  output Cout;
  
  wire c1, c2, c3;
  
  // 1st full adder
  full_adder fa1(.a(A[0]), .b(B[0]), .cin(Cin), .s(S[0]), .cout(c1));
  
  // 2nd full adder
  full_adder fa2(.a(A[1]), .b(B[1]), .cin(c1), .s(S[1]), .cout(c2));
  
  // 3rd full adder
  full_adder fa3(.a(A[2]), .b(B[2]), .cin(c2), .s(S[2]), .cout(c3));
  
  // 4th full adder
  full_adder fa4(.a(A[3]), .b(B[3]), .cin(c3), .s(S[3]), .cout(Cout));
  
endmodule

module full_adder (a, b, cin, s, cout);
  input a, b, cin;
  output s, cout;
  wire xor1, and1, and2;  // Intermediate signals used in the logic gates

  // Sum bit calculation
  xor gate1(xor1, a, b);  // Intermediate XOR result
  xor gate2(s, xor1, cin); // Final sum result

  // Carry-out bit calculation
  and gate3(and1, a, b);       // Intermediate AND result for a and b
  and gate4(and2, xor1, cin);  // Intermediate AND result for xor1 and cin
  or gate5(cout, and1, and2);  // Final carry-out result

endmodule
