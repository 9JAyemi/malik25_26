// SVA for red_pitaya_dfilt1
// Bind into DUT to access internals
module red_pitaya_dfilt1_sva (
  input logic               adc_clk_i,
  input logic               adc_rstn_i,
  input logic [13:0]        adc_dat_i,
  input logic [17:0]        cfg_aa_i,
  input logic [24:0]        cfg_bb_i,
  input logic [24:0]        cfg_kk_i,
  input logic [24:0]        cfg_pp_i,

  input logic [17:0]        cfg_aa_r,
  input logic [24:0]        cfg_bb_r,
  input logic [24:0]        cfg_kk_r,
  input logic [24:0]        cfg_pp_r,

  input logic [38:0]        bb_mult,
  input logic [32:0]        r2_sum,
  input logic [32:0]        r1_reg,
  input logic [22:0]        r2_reg,
  input logic [31:0]        r01_reg,
  input logic [27:0]        r02_reg,

  input logic [40:0]        aa_mult,
  input logic [48:0]        r3_sum,
  input logic [22:0]        r3_reg,

  input logic [39:0]        pp_mult,
  input logic [15:0]        r4_sum,
  input logic [14:0]        r4_reg,
  input logic [14:0]        r3_shr,

  input logic [39:0]        kk_mult,
  input logic [14:0]        r4_reg_r,
  input logic [14:0]        r4_reg_rr,
  input logic [13:0]        r5_reg,

  input logic [13:0]        adc_dat_o
);

  default clocking cb @(posedge adc_clk_i); endclocking
  default disable iff (!adc_rstn_i)

  // Config sampling (1-cycle pipe)
  assert property (cfg_aa_r == $past(cfg_aa_i));
  assert property (cfg_bb_r == $past(cfg_bb_i));
  assert property (cfg_kk_r == $past(cfg_kk_i));
  assert property (cfg_pp_r == $past(cfg_pp_i));

  // Stage 1/2 pipe relationships
  assert property (r01_reg == $past({adc_dat_i,18'h0})
                && r02_reg == $past(bb_mult[37:10])
                && r1_reg  == $past($signed(r02_reg) - $signed(r01_reg))
                && r2_reg  == $past(r2_sum[32:10]));

  // Stage 3 (IIR aa)
  assert property (r3_reg == $past(r3_sum[47:25]));

  // Stage 4 (pp) and delay line
  assert property (r3_shr   == $past(r3_reg[22:8])
                && r4_reg   == $past(r4_sum[14:0])
                && r4_reg_r == $past(r4_reg)
                && r4_reg_rr== $past(r4_reg_r));

  // Saturation and pass-through on kk path
  let kk_slice = $signed(kk_mult[38:24]);
  assert property ($past(kk_slice) >  $signed(14'sh1FFF) |-> r5_reg == 14'h1FFF);
  assert property ($past(kk_slice) <  $signed(14'sh2000) |-> r5_reg == 14'h2000);
  assert property (($past(kk_slice) <= $signed(14'sh1FFF)) &&
                   ($past(kk_slice) >= $signed(14'sh2000)) |-> r5_reg == $past(kk_mult[37:24]));

  // Output is wired to r5_reg
  assert property (adc_dat_o == r5_reg);

  // Synchronous reset clears all state on next cycle
  assert property ($past(!adc_rstn_i) |->
                   (r1_reg=='0 && r2_reg=='0 && r01_reg=='0 && r02_reg=='0 &&
                    r3_reg=='0 && r3_shr=='0 && r4_reg=='0 &&
                    r4_reg_r=='0 && r4_reg_rr=='0 && r5_reg=='0));

  // Coverage: reset, saturation hi/lo, and linear region
  cover property ($rose(adc_rstn_i));
  cover property (kk_slice >  $signed(14'sh1FFF) ##1 (r5_reg == 14'h1FFF));
  cover property (kk_slice <  $signed(14'sh2000) ##1 (r5_reg == 14'h2000));
  cover property ((kk_slice >= $signed(14'sh2000) && kk_slice <= $signed(14'sh1FFF))
                  ##1 (r5_reg == kk_mult[37:24]));
  cover property ($changed(r5_reg));

endmodule

bind red_pitaya_dfilt1 red_pitaya_dfilt1_sva sva_inst (.*);