module full_adder (
  input a,
  input b,
  input cin,
  output sum,
  output cout
);

  wire ha1_sum, ha1_carry, ha2_carry;

  // First half adder
  half_adder ha1 (
    .a(a),
    .b(b),
    .sum(ha1_sum),
    .carry(ha1_carry)
  );

  // Second half adder
  half_adder ha2 (
    .a(ha1_sum),
    .b(cin),
    .sum(sum),
    .carry(ha2_carry)
  );

  // Carry out is the OR of the two half adder carries
  assign cout = ha1_carry | ha2_carry;

endmodule
module half_adder (
  input a,
  input b,
  output sum,
  output carry
);

  assign sum = a ^ b;
  assign carry = a & b;

endmodule
