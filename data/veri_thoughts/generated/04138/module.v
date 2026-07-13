
module barrel_shifter #(
  parameter width = 8, // width of input signal
  parameter log2width = 3 // log base 2 of width
) (
  input [width-1:0] in,
  input [log2width-1:0] shift,
  output [width-1:0] out
);

  // temporary register for shifted input signal
  wire [width-1:0] shifted;
  integer i; // loop variable

  assign shifted = (shift == 0) ? in : in << shift;
  assign out = shifted;

endmodule