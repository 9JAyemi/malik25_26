module adder(
  input [7:0] A,
  input [7:0] B,
  output [7:0] S,
  output C
);

  wire [8:0] sum;
  
  assign sum = A + B;
  
  assign S = sum[7:0];
  assign C = sum[8];
  
endmodule