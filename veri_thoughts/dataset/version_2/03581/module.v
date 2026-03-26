module adder (
  input [3:0] A,
  input [3:0] B,
  output [3:0] sum
);

  assign sum = A + B;

endmodule