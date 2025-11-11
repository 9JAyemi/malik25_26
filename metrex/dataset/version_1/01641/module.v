module half_subtractor(
  input a,
  input b,
  output diff,
  output borrow
);

  assign diff = a ^ b;
  assign borrow = ~a & b;

endmodule

module full_subtractor(
  input a,
  input b,
  input c_in,
  output diff,
  output borrow
);

  wire temp_diff;
  wire temp_borrow1;
  wire temp_borrow2;

  half_subtractor ha1(a, b, temp_diff, temp_borrow1);
  half_subtractor ha2(temp_diff, c_in, diff, temp_borrow2);
  assign borrow = temp_borrow1 | temp_borrow2;

endmodule