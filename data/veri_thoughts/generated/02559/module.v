module four_bit_adder (
  input [3:0] A,
  input [3:0] B,
  input C,
  output [3:0] S
);

  // Declare internal wires
  wire [3:0] sum;
  wire [3:0] carry;

  // Generate sum and carry using basic gates
  assign sum = A ^ B;
  assign carry = A & B;

  // Output sum or carry based on control input C
  assign S = (C == 1'b0) ? sum : carry;

endmodule
