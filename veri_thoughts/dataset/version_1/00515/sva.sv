// SVA checker for compare_4
bind compare_4 compare_4_sva i_compare_4_sva (
  .ram_empty_fb_i_reg(ram_empty_fb_i_reg),
  .v1_reg(v1_reg),
  .rd_en(rd_en),
  .out(out),
  .comp1(comp1),
  .carrynet(carrynet),
  .comp0(comp0)
);

module compare_4_sva (
  input logic        ram_empty_fb_i_reg,
  input logic [4:0]  v1_reg,
  input logic        rd_en,
  input logic        out,
  input logic        comp1,
  input logic [3:0]  carrynet,
  input logic        comp0
);

  // Core functional equivalence
  assert property (carrynet == v1_reg[3:0]);
  assert property (comp0 == (|carrynet));
  assert property (ram_empty_fb_i_reg == !(comp0 & rd_en & out & comp1));
  assert property (ram_empty_fb_i_reg == !(rd_en & out & comp1 & (|v1_reg[3:0])));

  // Gating guarantee (any 0 input forces output 1)
  assert property ((!rd_en || !out || !comp1) |-> ram_empty_fb_i_reg);

  // Clean inputs => no X on internal/outputs
  assert property ((!$isunknown({v1_reg[3:0], rd_en, out, comp1})) |-> !$isunknown({carrynet, comp0, ram_empty_fb_i_reg}));

  // Independence from v1_reg[4]
  assert property ( $changed(v1_reg[4]) && $stable({v1_reg[3:0], rd_en, out, comp1})
                    |-> $stable({carrynet, comp0, ram_empty_fb_i_reg}) );

  // Coverage
  cover property (rd_en && out && comp1 && (v1_reg[3:0] != 4'h0) && (ram_empty_fb_i_reg == 1'b0)); // active low case
  cover property (rd_en && out && comp1 && (v1_reg[3:0] == 4'h0) && (ram_empty_fb_i_reg == 1'b1)); // zero nibble
  cover property (!rd_en || !out || !comp1);                                                      // any gate low
  cover property (v1_reg[3:0] == 4'hF);                                                           // all bits set
  cover property ($rose(comp0));
  cover property ($fell(comp0));

endmodule