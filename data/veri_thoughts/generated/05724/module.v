module sum_diff (
  input [7:0] A,
  input [7:0] B,
  output [7:0] S,
  output [7:0] D
);


  assign S = A + B;
  assign D = A - B;

endmodule