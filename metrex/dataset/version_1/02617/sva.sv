// SVA for cross_domain_sync
module cross_domain_sync_sva (
  input  logic s_axi_aclk,
  input  logic capturetrig1,
  input  logic read_Mux_In,
  input  logic captureTrig1_d0,
  input  logic s_level_out_d1_cdc_to,
  input  logic s_level_out_d2,
  input  logic s_level_out_d3,
  input  logic CaptureTrig1_int
);

  default clocking cb @(posedge s_axi_aclk); endclocking

  // Warm-up to avoid $past invalid cycles
  logic [4:0] warmup;
  always @(posedge s_axi_aclk) warmup <= {warmup[3:0], 1'b1};

  // Helper property
  property shift1(next, prev); next == $past(prev); endproperty

  // 4-stage synchronizer behaves like a shift register
  assert property (disable iff (!warmup[4]) shift1(s_level_out_d1_cdc_to, capturetrig1));
  assert property (disable iff (!warmup[4]) shift1(s_level_out_d2,       s_level_out_d1_cdc_to));
  assert property (disable iff (!warmup[4]) shift1(s_level_out_d3,       s_level_out_d2));
  assert property (disable iff (!warmup[4]) shift1(CaptureTrig1_int,     s_level_out_d3));

  // Steady-state alignment when source is stable
  assert property (disable iff (!warmup[4])
                   $stable(capturetrig1)[*4] |-> CaptureTrig1_int == $past(capturetrig1,4));

  // Gated capture: update only on trigger and to the sampled value of read_Mux_In
  assert property (disable iff (!warmup[4])
                   CaptureTrig1_int |-> ##0 (captureTrig1_d0 == read_Mux_In));

  // Hold when not triggered
  assert property (disable iff (!warmup[4])
                   !CaptureTrig1_int |-> ##0 $stable(captureTrig1_d0));

  // If read_Mux_In changes while enabled, captured value changes same edge
  assert property (disable iff (!warmup[4])
                   CaptureTrig1_int && $changed(read_Mux_In) |-> ##0 $changed(captureTrig1_d0));

  // No X/Z on key outputs after warm-up
  assert property (disable iff (!warmup[4])
                   !$isunknown({s_level_out_d1_cdc_to, s_level_out_d2, s_level_out_d3,
                                CaptureTrig1_int, captureTrig1_d0}));

  // Functional coverage
  cover property (disable iff (!warmup[4])
                  $changed(capturetrig1) ##1 $changed(s_level_out_d1_cdc_to)
                  ##1 $changed(s_level_out_d2) ##1 $changed(s_level_out_d3)
                  ##1 $changed(CaptureTrig1_int));

  cover property (disable iff (!warmup[4])
                  CaptureTrig1_int && (read_Mux_In==1'b1) ##0 (captureTrig1_d0==1'b1));
  cover property (disable iff (!warmup[4])
                  CaptureTrig1_int && (read_Mux_In==1'b0) ##0 (captureTrig1_d0==1'b0));

endmodule

// Bind into DUT
bind cross_domain_sync cross_domain_sync_sva sva (
  .s_axi_aclk(s_axi_aclk),
  .capturetrig1(capturetrig1),
  .read_Mux_In(read_Mux_In),
  .captureTrig1_d0(captureTrig1_d0),
  .s_level_out_d1_cdc_to(s_level_out_d1_cdc_to),
  .s_level_out_d2(s_level_out_d2),
  .s_level_out_d3(s_level_out_d3),
  .CaptureTrig1_int(CaptureTrig1_int)
);