module flip_flop_sva (
  input logic clk,
  input logic rst,
  input logic data,
  input logic q,
  input logic q_bar
);

  // During reset, outputs are complementary.
  reset_outputs_complement: assert property (
    @(posedge clk) rst |-> (q ^ q_bar) == 1'b1
  );

  // While reset stays asserted, outputs hold their values.
  reset_hold_stable: assert property (
    @(posedge clk) rst && $past(rst) |-> $stable(q) && $stable(q_bar)
  );

  // Immediately after reset deasserts, outputs are complementary.
  post_reset_complement: assert property (
    @(posedge clk) $past(rst) && !rst |-> (q ^ q_bar) == 1'b1
  );

  // If complement held last cycle, it holds this cycle (inductive step).
  complement_induction: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) |-> (q ^ q_bar) == 1'b1
  );

  // If q rises (with prior complement), q_bar falls the same cycle.
  edge_correlation_rise_fall: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) && $rose(q) |-> $fell(q_bar)
  );

  // If q falls (with prior complement), q_bar rises the same cycle.
  edge_correlation_fall_rise: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) && $fell(q) |-> $rose(q_bar)
  );

  // If q changes (with prior complement), q_bar changes the same cycle.
  change_correlation_q_to_qbar: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) && $changed(q) |-> $changed(q_bar)
  );

  // If q_bar changes (with prior complement), q changes the same cycle.
  change_correlation_qbar_to_q: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) && $changed(q_bar) |-> $changed(q)
  );

  // q rising and q_bar rising cannot happen together (with prior complement).
  no_simultaneous_rise: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) && $rose(q) |-> !$rose(q_bar)
  );

  // q falling and q_bar falling cannot happen together (with prior complement).
  no_simultaneous_fall: assert property (
    @(posedge clk) disable iff (rst) $past((q ^ q_bar) == 1'b1) && $fell(q) |-> !$fell(q_bar)
  );

endmodule