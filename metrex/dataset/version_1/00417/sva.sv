// SVA for d_ff_async_reset
// Bind this checker to the DUT

module d_ff_async_reset_sva (input logic clk, reset, d, q);

  default clocking cb @(posedge clk or negedge reset); endclocking

  // Async reset must clear q immediately (after NBA update)
  a_async_clear: assert property (@(negedge reset) ##0 (q == 1'b0));

  // While reset is low, q must be 0 at all observation points
  a_hold_low:   assert property ( (!reset) |-> (q == 1'b0) );

  // When reset is high, q captures d on the rising clock
  a_sync_cap:   assert property (@(posedge clk) reset |=> (q == $past(d)));

  // q should never be X/Z at observed events
  a_q_known:    assert property ( !$isunknown(q) );

  // Safety: avoid coincident clk rising edge with reset falling edge
  a_no_overlap: assert property (@(posedge clk) !$fell(reset));

  // Coverage
  c_rst_assert:    cover property (@(negedge reset) 1);
  c_rst_deassert:  cover property (@(posedge  reset) 1);
  c_cap0:          cover property (@(posedge clk) reset && (d==1'b0) ##1 (q==1'b0));
  c_cap1:          cover property (@(posedge clk) reset && (d==1'b1) ##1 (q==1'b1));
  c_q_toggle:      cover property (@(posedge clk) reset ##1 $changed(q));

endmodule

bind d_ff_async_reset d_ff_async_reset_sva sva_i (.clk(clk), .reset(reset), .d(d), .q(q));