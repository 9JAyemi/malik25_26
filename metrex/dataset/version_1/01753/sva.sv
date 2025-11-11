// SVA for synchronous_reset
module synchronous_reset_sva (
  input wire clk,
  input wire out,
  input wire in0,
  input wire AS
);
  default clocking cb @(posedge clk); endclocking

  // Sequences for multi-clock use
  sequence next_clk; @(posedge clk) 1; endsequence

  // Async reset asserts immediately
  assert property (@(negedge in0) AS == 1'b0);

  // While reset is active, AS is held low on every clk edge
  assert property (@(posedge clk) !in0 |-> AS == 1'b0);

  // After reset release, AS stays low until the next clk edge
  assert property (@(posedge in0) AS == 1'b0 until_with next_clk);

  // When reset is high on two consecutive clk edges, AS follows out (1-cycle latency)
  assert property (@(posedge clk) disable iff (!in0) $past(in0) |-> AS == $past(out));

  // AS may only change on a clk posedge or a reset negedge (no glitches)
  assert property (@(posedge AS or negedge AS) $rose(clk) or $fell(in0));

  // No X/Z on AS in normal operation
  assert property (@(posedge clk) disable iff (!in0) !$isunknown(AS));

  // Coverage
  cover property (@(negedge in0) 1);          // reset assert
  cover property (@(posedge in0) 1);          // reset deassert
  cover property (@(posedge clk) disable iff (!in0) $rose(AS));
  cover property (@(posedge clk) disable iff (!in0) $fell(AS));
endmodule

bind synchronous_reset synchronous_reset_sva sva_i(.clk(clk), .out(out), .in0(in0), .AS(AS));