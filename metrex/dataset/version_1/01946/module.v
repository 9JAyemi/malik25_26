module HalfSubtractor (
  input A,
  input B,
  output difference,
  output borrow
);
  
  assign difference = A ^ B;
  assign borrow = ~A & B;
  
endmodule

module FullSubtractor (
  input A,
  input B,
  input borrow,
  output difference,
  output borrow_out
);
  
  wire temp_diff1, temp_diff2, temp_borrow1, temp_borrow2;
  
  HalfSubtractor HS1(.A(A), .B(B), .difference(temp_diff1), .borrow(temp_borrow1));
  HalfSubtractor HS2(.A(temp_diff1), .B(borrow), .difference(difference), .borrow(temp_borrow2));
  assign borrow_out = temp_borrow1 | temp_borrow2;
  
endmodule