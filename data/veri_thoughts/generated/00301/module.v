
module full_adder (
  input A, 
  input B, 
  input Cin, 
  output S, 
  output Cout
);

  wire n1, n2, n3, n4, n5;

  xor (S, n1, Cin);
  xor (n1, A, B);
  and (n2, A, B);
  and (n3, n1, Cin);
  or (Cout, n2, n3);

endmodule