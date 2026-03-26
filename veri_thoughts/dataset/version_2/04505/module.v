module half_subtractor (
  input A,
  input B,
  output DIFF,
  output BORROW
);

  assign DIFF = A ^ B;
  assign BORROW = A < B;

endmodule

module full_subtractor (
  input A,
  input B,
  input BORROW_IN,
  output DIFF,
  output BORROW
);

  wire DIFF1, BORROW1, DIFF2, BORROW2;

  half_subtractor HS1(.A(A), .B(B), .DIFF(DIFF1), .BORROW(BORROW1));
  half_subtractor HS2(.A(DIFF1), .B(BORROW_IN), .DIFF(DIFF2), .BORROW(BORROW2));

  assign DIFF = DIFF2;
  assign BORROW = BORROW1 | BORROW2;

endmodule