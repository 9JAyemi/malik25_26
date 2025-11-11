// SVA for binary_counter: concise, high-quality checks and coverage
module binary_counter_sva #(parameter WIDTH=4)
(
  input logic              clk,
  input logic              reset,
  input logic [WIDTH-1:0]  Q
);

  default clocking cb @(posedge clk); endclocking

  // Async reset must clear Q (after NBAs)
  assert property (@(posedge reset) ##0 (Q == '0 && !$isunknown(Q)))
    else $error("Q not cleared on async reset");

  // While reset is asserted at a clk edge, Q is 0 (after NBAs)
  assert property (reset |-> ##0 (Q == '0 && !$isunknown(Q)))
    else $error("Q not 0 while reset asserted");

  // Normal increment when reset is low in consecutive cycles (after NBAs)
  assert property ((!reset && !$past(reset)) |-> ##0 (Q == $past(Q)+1))
    else $error("Q did not increment by 1 when out of reset");

  // First cycle after reset deasserts: Q goes 0 -> 1 (after NBAs)
  assert property ($fell(reset) |-> ##0 ($past(Q) == '0 &&
                                         Q == {{(WIDTH-1){1'b0}},1'b1}))
    else $error("Q did not start at 1 after reset release");

  // Explicit wrap-around check (after NBAs)
  assert property ((!reset && !$past(reset) && $past(Q) == {WIDTH{1'b1}}) |-> ##0 (Q == '0))
    else $error("Q failed to wrap from max to 0");

  // No X/Z on Q at each clk (after NBAs)
  assert property (##0 !$isunknown(Q))
    else $error("Q has X/Z");

  // Coverage
  cover property (@(posedge clk) $rose(reset));
  cover property (@(posedge clk) $fell(reset));
  cover property ((!reset && !$past(reset)) |-> ##0 (Q == $past(Q)+1));
  cover property ((!reset && !$past(reset) && $past(Q) == {WIDTH{1'b1}}) |-> ##0 (Q == '0));
endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva #(.WIDTH(4)) u_binary_counter_sva (
  .clk  (clk),
  .reset(reset),
  .Q    (Q)
);