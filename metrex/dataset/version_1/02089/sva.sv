// SVA for d_flip_flop_mux_latch
module d_flip_flop_mux_latch_sva (
  input logic clk,
  input logic d,
  input logic q,
  input logic mux_out,
  input logic latch_out
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Functional checks
  property p_mux_captures_d;
    past_valid |-> (mux_out == $past(d));
  endproperty
  assert property (p_mux_captures_d);

  property p_latch_tracks_mux_at_clk;
    past_valid |-> (latch_out == mux_out);
  endproperty
  assert property (p_latch_tracks_mux_at_clk);

  property p_q_is_d_one_cycle_late;
    past_valid |-> (q == $past(d));
  endproperty
  assert property (p_q_is_d_one_cycle_late);

  property p_q_samples_latch_at_clk;
    past_valid |-> (q == $past(latch_out));
  endproperty
  assert property (p_q_samples_latch_at_clk);

  // Change/glitch discipline (clockless)
  property p_mux_changes_only_on_clk;
    @($global_clock) $changed(mux_out) |-> $rose(clk);
  endproperty
  assert property (p_mux_changes_only_on_clk);

  property p_q_changes_only_on_clk;
    @($global_clock) $changed(q) |-> $rose(clk);
  endproperty
  assert property (p_q_changes_only_on_clk);

  property p_latch_changes_only_with_mux;
    @($global_clock) $changed(latch_out) |-> $changed(mux_out);
  endproperty
  assert property (p_latch_changes_only_with_mux);

  // Coverage
  cover property (past_valid && $rose(d) ##1 (q == 1'b1));
  cover property (past_valid && $fell(d) ##1 (q == 1'b0));
  cover property (past_valid && (d == 1'b1) ##1 (q == 1'b1));
  cover property (past_valid && (d == 1'b0) ##1 (q == 1'b0));

endmodule

// Bind into the DUT
bind d_flip_flop_mux_latch d_flip_flop_mux_latch_sva sva_i (
  .clk(clk),
  .d(d),
  .q(q),
  .mux_out(mux_out),
  .latch_out(latch_out)
)