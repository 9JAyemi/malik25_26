module and_gate (
  input A,
  input B,
  output Y
);

  wire A1, A2, B1, B2;
  
  assign A1 = A;
  assign A2 = 1'b1;
  assign B1 = B;
  assign B2 = 1'b1;

  assign Y = A & B;

endmodule