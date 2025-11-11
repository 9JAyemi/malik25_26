// SVA for rp_adc. Bind this to the DUT.
// Focus: constant outputs, register sampling, output transform, X-propagation, and basic coverage.

module rp_adc_sva
(
  input  logic [13:0] adc_dat_a_i,
  input  logic [13:0] adc_dat_b_i,
  input  logic        adc_clk,
  input  logic        adc_rst_i,
  input  logic [1:0]  adc_clk_source,
  input  logic        adc_cdcs_o,
  input  logic [13:0] adc_dat_a_o,
  input  logic [13:0] adc_dat_b_o
);

  // Establish a clean $past domain (don’t rely on DUT reset behavior)
  logic past_v;
  always @(posedge adc_clk or posedge adc_rst_i) begin
    if (adc_rst_i) past_v <= 1'b0;
    else           past_v <= 1'b1;
  end

  default clocking cb @(posedge adc_clk); endclocking
  default disable iff (!past_v);

  // 1) Constants
  ap_const_cdcs:       assert property (adc_cdcs_o == 1'b1);
  ap_const_clk_source: assert property (adc_clk_source == 2'b10);

  // 2) Registered sampling and combinational transform to outputs
  //    adc_dat_*_o = { MSB passthrough of prior input, bitwise invert of prior input lower bits }
  ap_a_transform: assert property (
    adc_dat_a_o[13]   == $past(adc_dat_a_i[13]) &&
    adc_dat_a_o[12:0] == ~$past(adc_dat_a_i[12:0])
  );

  ap_b_transform: assert property (
    adc_dat_b_o[13]   == $past(adc_dat_b_i[13]) &&
    adc_dat_b_o[12:0] == ~$past(adc_dat_b_i[12:0])
  );

  // 3) X-propagation guards on outputs when inputs are known
  ap_a_no_x: assert property (
    !$isunknown($past(adc_dat_a_i)) |-> !$isunknown(adc_dat_a_o)
  );

  ap_b_no_x: assert property (
    !$isunknown($past(adc_dat_b_i)) |-> !$isunknown(adc_dat_b_o)
  );

  ap_const_no_x: assert property (!$isunknown(adc_cdcs_o) && !$isunknown(adc_clk_source));

  // 4) Lightweight coverage
  //    - See at least one correct transform on each channel
  //    - See both MSB polarities exercised
  cp_a_transform: cover property (
    adc_dat_a_o[13]   == $past(adc_dat_a_i[13]) &&
    adc_dat_a_o[12:0] == ~$past(adc_dat_a_i[12:0])
  );

  cp_b_transform: cover property (
    adc_dat_b_o[13]   == $past(adc_dat_b_i[13]) &&
    adc_dat_b_o[12:0] == ~$past(adc_dat_b_i[12:0])
  );

  cp_a_msb0: cover property ($past(adc_dat_a_i[13]) == 1'b0 && adc_dat_a_o[13] == 1'b0);
  cp_a_msb1: cover property ($past(adc_dat_a_i[13]) == 1'b1 && adc_dat_a_o[13] == 1'b1);
  cp_b_msb0: cover property ($past(adc_dat_b_i[13]) == 1'b0 && adc_dat_b_o[13] == 1'b0);
  cp_b_msb1: cover property ($past(adc_dat_b_i[13]) == 1'b1 && adc_dat_b_o[13] == 1'b1);

endmodule

// Bind to all instances of rp_adc
bind rp_adc rp_adc_sva sva_i (.*);