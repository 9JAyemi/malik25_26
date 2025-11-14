// SVA for ad_rst. Bind into the DUT to check internal pipeline and end-to-end behavior.

module ad_rst_sva (
  input  logic clk,
  input  logic preset,
  input  logic rst,
  input  logic ad_rst_sync_m1,
  input  logic ad_rst_sync
);
  default clocking cb @(posedge clk); endclocking

  // Knownness on synchronous flops
  a_known_sync_flops: assert property ( !$isunknown({rst, ad_rst_sync, ad_rst_sync_m1}) );

  // Exact 3-stage shift behavior (stage-by-stage including input sampling)
  a_shift_exact: assert property (
    {rst, ad_rst_sync, ad_rst_sync_m1} ==
      $past({ad_rst_sync, ad_rst_sync_m1, preset}, 1, 3'b000)
  );

  // End-to-end latency: rst equals preset delayed by 3 clocks
  a_latency3: assert property ( rst == $past(preset, 3, 1'b0) );

  // Edge correspondence (both directions, no spurious edges)
  a_rise_delay_exact: assert property ( $rose(preset) |-> ##3 $rose(rst) );
  a_fall_delay_exact: assert property ( $fell(preset) |-> ##3 $fell(rst) );
  a_rise_no_spurious: assert property ( $rose(rst)   |-> $past($rose(preset), 3) );
  a_fall_no_spurious: assert property ( $fell(rst)   |-> $past($fell(preset), 3) );

  // Coverage: basic edge propagation and a single-cycle pulse propagation
  c_rise:      cover property ( $rose(preset) ##3 $rose(rst) );
  c_fall:      cover property ( $fell(preset) ##3 $fell(rst) );
  c_1clk_pulse: cover property (
    $rose(preset) ##1 $fell(preset) ##3 $rose(rst) ##1 $fell(rst)
  );
endmodule

bind ad_rst ad_rst_sva sva_ad_rst (.*);