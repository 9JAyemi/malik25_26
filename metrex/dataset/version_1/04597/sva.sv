// SVA for sync_module
module sync_module_sva;

  // Access DUT signals via bind scope
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset must clear immediately on negedge reset_n
  ap_async_clear_immediate: assert property (@(negedge reset_n) (data_out==1'b0 && data_in_d1==1'b0));

  // While in reset, flops hold 0 (checked each clk)
  ap_hold_during_reset:    assert property (!reset_n |-> (data_out==1'b0 && data_in_d1==1'b0));

  // First cycle after reset release, data_out stays 0
  ap_first_after_release:  assert property ($rose(reset_n) |-> (data_out==1'b0));

  // One-cycle pipeline behavior during run
  ap_out_latency:          assert property (reset_n && $past(reset_n) |-> (data_out   == $past(data_in)));
  ap_stage1_latency:       assert property (reset_n && $past(reset_n) |-> (data_in_d1 == $past(data_in)));

  // No X/Z in reset and in run
  ap_no_x_in_reset:        assert property (!reset_n |-> (!$isunknown(data_out) && !$isunknown(data_in_d1)));
  ap_no_x_in_run:          assert property (reset_n && $past(reset_n) |-> (!$isunknown(data_out) && !$isunknown(data_in_d1)));

  // Coverage
  cv_async_reset_assert:   cover  property (@(negedge reset_n) 1);
  cv_reset_release:        cover  property ($rose(reset_n));
  cv_rise_propagates:      cover  property (reset_n && $past(reset_n) && $rose(data_in) ##1 (data_out==1));
  cv_fall_propagates:      cover  property (reset_n && $past(reset_n) && $fell(data_in) ##1 (data_out==0));

endmodule

// Bind into the DUT
bind sync_module sync_module_sva sva_sync_module_i();