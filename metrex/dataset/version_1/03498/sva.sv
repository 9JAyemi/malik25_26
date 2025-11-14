// SVA for dffc_64: synchronous reset, q captures d on each posedge clk when not in reset
module dffc_64_sva (
  input logic        clk,
  input logic        reset,
  input logic [63:0] d,
  input logic [63:0] q
);
  // establish past-valid after first clock to safely use $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic health checks
  a_reset_known:      assert property (!$isunknown(reset));
  a_q_known:          assert property (!$isunknown(q));

  // Reset behavior: if reset is 1 at a posedge, next-state q is zero
  a_rst_clears_q:     assert property (reset |=> (q == 64'h0));

  // While reset is held, q stays zero
  a_rst_hold_zero:    assert property (reset && $past(reset) |-> (q == 64'h0));

  // Normal capture: when previous cycle not in reset, q equals previous d
  a_q_tracks_d:       assert property (!$past(reset) |-> (q == $past(d)));

  // No mid-cycle glitches: q changes only on posedge clk
  a_no_mid_glitch:    assert property (@(negedge clk) disable iff (!past_valid) $stable(q));

  // Coverage
  c_seen_reset:       cover  property (reset);
  c_reset_deassert:   cover  property ($fell(reset));
  c_data_capture:     cover  property (!$past(reset) && (d != $past(d)) ##1 (q == $past(d)));
  c_hold_zero_multi:  cover  property (reset [*2] ##1 (q == 64'h0));
endmodule

// Bind to DUT
bind dffc_64 dffc_64_sva u_dffc_64_sva (.clk(clk), .reset(reset), .d(d), .q(q));