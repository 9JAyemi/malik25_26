
module bitwise_operation(x, y, out);
  // IO ports
  input  [15:0] x, y;
  output [15:0] out;

  // Net declarations
  wire [15:0] and_n, or_n, not_n, xor_n;
  wire [2:0] func;

  // Assignments
  assign func = 3'b010; // Select NOT operation
  assign and_n  = x & y;
  assign or_n   = x | y;
  assign not_n  = ~x;
  assign xor_n  = x ^ y;
  assign out = not_n;

endmodule