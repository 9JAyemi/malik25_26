// SVA for bus_hold. Bind to the DUT to gain access to internal reg.
module bus_hold_sva #(parameter int n = 8)
(
  input logic                 clk,
  input logic                 reset,
  input logic [n-1:0]         bus_in,
  input logic [n-1:0]         bus_out
);
  default clocking cb @(posedge clk); endclocking

  // ensure $past is safe
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Assertions

  // Reset forces output low (combinational gating)
  a_reset_out_zero: assert property (reset |-> (bus_out == '0));

  // Output equals the registered value whenever not in reset
  a_out_eq_reg:     assert property (!reset |-> (bus_out == bus_hold_reg));

  // After any cycle with reset=1, the register must read as 0 on the next sample
  a_reg_zero_after_reset: assert property (past_valid && $past(reset) |-> (bus_hold_reg == '0));

  // While staying in reset, reg remains 0 and output stays 0/stable
  a_reg_zero_during_reset: assert property (past_valid && reset && $past(reset) |-> (bus_hold_reg == '0));
  a_out_stable_reset:      assert property (past_valid && reset && $past(reset) |-> ($stable(bus_out) && bus_out == '0));

  // When not in reset on consecutive cycles, register captures bus_in and output reflects prior-cycle bus_in
  a_reg_captures_in: assert property (past_valid && !reset && $past(!reset) |-> (bus_hold_reg == $past(bus_in)));
  a_out_tracks_in:   assert property (past_valid && !reset && $past(!reset) |-> (bus_out     == $past(bus_in)));

  // No X on output when prior-cycle input was known and not in reset
  a_out_known_when_in_known: assert property (
    past_valid && !reset && $past(!reset) && !$isunknown($past(bus_in)) |-> !$isunknown(bus_out)
  );

  // Coverage

  // Observe reset assert/deassert and a subsequent capture
  c_reset_sequence: cover property (reset ##1 !reset ##1 $changed(bus_in) ##1 (bus_out == $past(bus_in)));

  // Observe normal capture on input change
  c_capture_change: cover property (!reset ##1 $changed(bus_in) ##1 (bus_out == $past(bus_in)));

endmodule

// Bind into the DUT (tools allow direct reference to internal bus_hold_reg)
bind bus_hold bus_hold_sva #(.n(n)) i_bus_hold_sva (.clk(clk), .reset(reset), .bus_in(bus_in), .bus_out(bus_out));