// SVA for bus_hold. Bind this to the DUT.
// Focus: reset behavior, registered transfer, X-safety, and basic coverage.

module bus_hold_sva #(parameter n=8)
(
  input logic                 clk,
  input logic                 reset,
  input logic [n-1:0]         bus_in,
  input logic [n-1:0]         bus_out
);

  default clocking cb @(posedge clk); endclocking

  // Reset forces bus_out to zero (combinational gate observed at clock)
  a_reset_forces_zero: assert property (reset |-> bus_out == '0);

  // On reset deassertion cycle, bus_out still zero (reg was cleared)
  a_deassert_cycle_zero: assert property ($fell(reset) |-> bus_out == '0);

  // Registered behavior: when not in reset in consecutive cycles,
  // bus_out equals previous cycle's bus_in (1-cycle latency in SVA sampling)
  a_reg_behavior: assert property (!reset && !$past(reset) |-> bus_out == $past(bus_in));

  // X-safety
  a_reset_known:  assert property (!$isunknown(reset));
  a_out_no_x_when_active: assert property (!reset |-> !$isunknown(bus_out));

  // Optional: change in bus_in propagates to bus_out next cycle (when staying out of reset)
  a_change_propagates: assert property (!reset && !$past(reset) && $changed($past(bus_in)) |-> $changed(bus_out));

  // Coverage
  c_reset_pulse:     cover property (reset ##1 !reset);
  c_track_sample:    cover property (!reset && !$past(reset) && bus_out == $past(bus_in));
  c_out_toggles:     cover property (!reset && $changed(bus_out));

endmodule

// Bind to DUT
bind bus_hold bus_hold_sva #(.n(n)) bus_hold_sva_b (.clk(clk), .reset(reset), .bus_in(bus_in), .bus_out(bus_out));