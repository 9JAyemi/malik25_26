// SVA for decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_rd_status_flags_ss and
// decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_rd_bin_cntr
// Bind these modules to the DUTs below.

////////////////////////////////////////////////////////////
// Assertions for rd_status_flags_ss
////////////////////////////////////////////////////////////
module sva_rd_status_flags_ss (
  input logic clk,
  input logic rd_en,
  input logic empty,
  input logic ram_full_fb_i_reg,
  input logic ram_full_fb_i_reg_0,
  input logic out,
  input logic rsts
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Sanity: no X on key inputs/outputs
  assert property (!$isunknown({rd_en, empty, ram_full_fb_i_reg, ram_full_fb_i_reg_0, out, rsts}));

  // out is registered version of (rd_en && !empty)
  assert property (out == $past(rd_en && !empty));

  // rsts next-state function with priority: read clears rsts, else full_fb sets rsts, else hold
  assert property (
    rsts == ( $past(rd_en && !empty) ? 1'b0
            : ($past(ram_full_fb_i_reg && !ram_full_fb_i_reg_0) ? 1'b1
            : $past(rsts)))
  );

  // Explicit priority when both conditions true (redundant but clear)
  assert property ($past(rd_en && !empty && ram_full_fb_i_reg && !ram_full_fb_i_reg_0) |-> rsts == 1'b0);

  // Coverage
  cover property ($past(rd_en && !empty) && out);                       // out asserted
  cover property ($past(ram_full_fb_i_reg && !ram_full_fb_i_reg_0) &&   // rsts set
                  !$past(rd_en && !empty) && rsts);
  cover property ($past(rd_en && !empty && ram_full_fb_i_reg && !ram_full_fb_i_reg_0) && // priority case
                  rsts == 1'b0);
  cover property (!$past(rd_en && !empty) &&
                  !$past(ram_full_fb_i_reg && !ram_full_fb_i_reg_0) &&
                  rsts == $past(rsts));                                  // hold case
endmodule

bind decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_rd_status_flags_ss
  sva_rd_status_flags_ss
  u_sva_rd_status_flags_ss(
    .clk(clk),
    .rd_en(rd_en),
    .empty(empty),
    .ram_full_fb_i_reg(ram_full_fb_i_reg),
    .ram_full_fb_i_reg_0(ram_full_fb_i_reg_0),
    .out(out),
    .rsts(rsts)
  );

////////////////////////////////////////////////////////////
// Assertions for rd_bin_cntr
////////////////////////////////////////////////////////////
module sva_rd_bin_cntr (
  input  logic        clk,
  input  logic        rd_en,
  input  logic        ram_empty_i_reg,
  input  logic [1:0]  count,
  input  logic [0:0]  AR,
  input  logic [7:0]  ram,
  input  logic [5:0]  Q
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Sanity: no X on used inputs/outputs
  assert property (!$isunknown({rd_en, ram_empty_i_reg, count, AR, ram, Q}));

  // Update rule: on read, Q == zero-extended ram bit at index; else hold previous Q
  assert property (
    Q == ( $past(rd_en && !ram_empty_i_reg)
           ? {5'b0, $past(ram[count+AR])}
           : $past(Q))
  );

  // Index stays within RAM width when read fires (should always hold)
  assert property ($past(rd_en && !ram_empty_i_reg) |-> ($past(count+AR) <= 7));

  // Coverage
  cover property ($past(rd_en && !ram_empty_i_reg) && Q == 6'b000001);
  cover property ($past(rd_en && !ram_empty_i_reg) && Q == 6'b000000);
  cover property (!$past(rd_en && !ram_empty_i_reg) && Q == $past(Q)); // hold
endmodule

bind decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_rd_bin_cntr
  sva_rd_bin_cntr
  u_sva_rd_bin_cntr(
    .clk(clk),
    .rd_en(rd_en),
    .ram_empty_i_reg(ram_empty_i_reg),
    .count(count),
    .AR(AR),
    .ram(ram),
    .Q(Q)
  );