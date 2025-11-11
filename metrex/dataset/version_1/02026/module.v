module bitwise_operators #(
  parameter n = 4
) (
  input [n-1:0] A,
  input [n-1:0] B,
  output [n-1:0] C1,
  output [n-1:0] C2,
  output [n-1:0] C3,
  output [n-1:0] C4

);

// Bitwise AND
assign C1 = A & B;

// Bitwise OR
assign C2 = A | B;

// Bitwise XOR
assign C3 = A ^ B;

// Bitwise NOT
assign C4 = ~A;

endmodule