module multiplier_block (
    i_data0,
    o_data0
);

  // Port mode declarations:
  input   [31:0] i_data0;
  output  [31:0]
    o_data0;

  //Multipliers:

  wire [31:0]
    w1,
    w2048,
    w2049,
    w8196,
    w6147,
    w64,
    w6211,
    w24844;

  assign w1 = i_data0;
  assign w2048 = w1 << 11;
  assign w2049 = w1 + w2048;
  assign w64 = w1 << 6;
  assign w8196 = w2049 << 2;
  assign w6147 = w8196 - w2049;
  assign w6211 = w6147 + w64;
  assign w24844 = w6211 << 2;

  assign o_data0 = w24844;

  //multiplier_block area estimate = 4886.48160088529;
endmodule