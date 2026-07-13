module full_adder (
  input a,
  input b,
  input cin,
  output s,
  output cout
);

  wire c1, c2;

  assign s = a ^ b ^ cin;
  assign c1 = a & b;
  assign c2 = cin & (a ^ b);
  assign cout = c1 | c2;

endmodule
