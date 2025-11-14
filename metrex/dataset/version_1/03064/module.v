
module half_full_adder (
  input A,
  input B,
  input carry_in,
  output sum,
  output carry_out
);

  // Instantiate Half Adder
  wire sum_int;
  wire carry_int;
  half_adder HA (
    .A(A),
    .B(B),
    .sum(sum_int),
    .carry(carry_int)
  );

  // Instantiate Full Adder
  assign sum = sum_int ^ carry_in;
  assign carry_out = carry_int | (sum_int & carry_in);

endmodule
module half_adder (
  input A,
  input B,
  output sum,
  output carry
);

  assign sum = A ^ B;
  assign carry = A & B;

endmodule
module full_adder (
  input A,
  input B,
  input carry_in,
  output sum,
  output carry_out
);

  assign sum = A ^ B ^ carry_in;
  assign carry_out = (A & B) | (B & carry_in) | (A & carry_in);

endmodule