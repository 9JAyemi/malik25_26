
module HAX1(
  input A,
  input B,
  output YC,
  output YS
);

assign YC = A & B;
assign YS = A ^ B;

endmodule
