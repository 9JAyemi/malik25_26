module half_adder (
  input a,
  input b,
  output sum,
  output carry
);

  assign sum = a ^ b;
  assign carry = a & b;

endmodule

module full_adder (
  input a,
  input b,
  input c_in,
  output sum,
  output c_out
);

  wire s1, s2, c1, c2;

  half_adder ha1 (.a(a), .b(b), .sum(s1), .carry(c1));
  half_adder ha2 (.a(s1), .b(c_in), .sum(sum), .carry(c2));
  assign c_out = c1 | c2;

endmodule