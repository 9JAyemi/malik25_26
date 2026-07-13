
module three_input_full_adder (input A, input B, input C, output S, output Cout);
  wire n1, n2, n3;

  xor U1 (n1, A, B);
  xor U2 (S, n1, C);
  and U3 (n2, A, B);
  and U4 (n3, n1, C);
  or U5 (Cout, n2, n3);
endmodule