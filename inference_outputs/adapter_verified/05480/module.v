
module adder(A, B, C, CO);
  input [3:0] A, B;
  output [3:0] C;
  output CO;

  wire [4:0] sum;  // Changed from [3:0] to [4:0] to accommodate the carry-out bit

  assign sum = A + B;
  assign C = sum[3:0];
  assign CO = sum[4];

endmodule