module multiplier_block (
    i_data0,
    o_data0
);

  // Port mode declarations:
  input   [31:0] i_data0;
  output  [31:0] o_data0;

  // Multipliers:
  wire [31:0] w1, w256, w257, w4, w32, w229, w261, w29312;

  assign w1 = i_data0;
  assign w256 = i_data0 << 8;
  assign w257 = w1 + w256;
  assign w4 = i_data0 << 2;
  assign w32 = i_data0 << 5;
  assign w261 = w257 + w4;
  assign w229 = w261 - w32;
  assign w29312 = w229 << 7;

  assign o_data0 = w29312;

  // Multiplier block area estimate = 4204.56962668382;
endmodule