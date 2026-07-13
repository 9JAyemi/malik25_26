
module barrel_shifter(
  input [3:0] in,
  input [1:0] shift,
  input dir,
  output [3:0] out
);

  wire [3:0] shifted_right;
  wire [3:0] shifted_left;

  assign shifted_right = {in[1:0], 2'b00};
  assign shifted_left = {2'b00, in[3:2]};

  assign out = (dir == 0) ? shifted_right >> shift : shifted_left << shift;

endmodule
