
module compare_4 (
  ram_empty_fb_i_reg,
  v1_reg,
  rd_en,
  out,
  comp1
);

  output ram_empty_fb_i_reg;
  input [4:0] v1_reg;
  input rd_en;
  input out;
  input comp1;

  wire [3:0] carrynet;
  wire comp0;
  wire ram_empty_fb_i_reg;
  wire rd_en;
  wire [4:0] v1_reg;

  // Carry Look-Ahead Adder
  assign carrynet = {1'b0, 1'b0, 1'b0, 1'b0} + v1_reg[3:0];

  // 4-input LUT
  assign ram_empty_fb_i_reg = !(comp0 & rd_en & out & comp1);
  assign comp0 = carrynet[3] | carrynet[2] | carrynet[1] | carrynet[0];

endmodule
