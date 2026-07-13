module binary_counter_sva
#(parameter MAX_COUNT = 15)
(
  input logic       clk,
  input logic       reset,
  input logic [3:0] count,
  input logic       overflow
);

  // A sampled reset drives both outputs low by the next sampled cycle.
  check_reset_clears_outputs: assert property (
    @(posedge clk) reset |=> (count == 4'd0 && overflow == 1'b0)
  );

  // A sampled terminal count always rolls the count back to zero.
  check_terminal_count_rolls_to_zero: assert property (
    @(posedge clk) disable iff (reset)
    (count == MAX_COUNT) |=> (count == 4'd0)
  );

  // A sampled non-terminal count advances by one, or is driven to zero by reset.
  check_nonterminal_count_progress: assert property (
    @(posedge clk) disable iff (reset)
    (count != MAX_COUNT) |=> ((count == ($past(count) + 4'd1)) || (count == 4'd0))
  );

  // A sampled non-terminal count clears overflow on the next cycle.
  check_nonterminal_clears_overflow: assert property (
    @(posedge clk) disable iff (reset)
    (count != MAX_COUNT) |=> (overflow == 1'b0)
  );

  // Any observed overflow must come from a terminal count on the prior sampled cycle.
  check_overflow_follows_terminal_count: assert property (
    @(posedge clk) disable iff (reset)
    1'b1 |=> (!overflow || ($past(count) == MAX_COUNT))
  );

  // Any observed overflow is accompanied by a zero count.
  check_overflow_implies_zero_count: assert property (
    @(posedge clk) disable iff (reset)
    1'b1 |=> (!overflow || (count == 4'd0))
  );

endmodule