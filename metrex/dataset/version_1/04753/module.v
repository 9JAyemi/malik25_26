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
    w32,
    w33,
    w4096,
    w4129,
    w2,
    w4131,
    w264,
    w4395,
    w8790;

  assign w1 = i_data0;
  assign w2 = w1 << 1;
  assign w32 = w1 << 5;
  assign w33 = w1 + w32;
  assign w4096 = w1 << 12;
  assign w4129 = w33 + w4096;
  assign w4131 = w4129 + w2;
  assign w264 = w33 << 3;
  assign w4395 = w4131 + w264;
  assign w8790 = w4395 << 1;

  assign o_data0 = w8790;

  //multiplier_block area estimate = 7035.33617542206;
endmodule