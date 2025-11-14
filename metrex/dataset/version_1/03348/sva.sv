// SVA for counter. Bind this to the DUT.
// Focused, high-quality checks + essential coverage.

module counter_sva #(parameter int n = 4)
(
  input logic               clk,
  input logic               rst,
  input logic [n-1:0]       count
);

  default clocking cb @(posedge clk); endclocking
  localparam logic [n-1:0] MASK = {n{1'b1}};
  localparam logic [n-1:0] ZERO = {n{1'b0}};
  localparam logic [n-1:0] ONE  = {{(n-1){1'b0}},1'b1};

  // Async reset must clear immediately on posedge rst
  a_rst_async: assert property (@(posedge rst) count == ZERO);

  // While rst is asserted at clk edge, count must be 0 and known
  a_rst_sync:  assert property (rst |-> (count == ZERO && !$isunknown(count)));

  // After deassertion (previous cycle rst=1, now 0), first count must be 1
  a_first_after_release: assert property ($fell(rst) |-> count == ONE);

  // When not in reset for consecutive cycles, counter increments modulo 2^n
  a_inc_mod: assert property (!rst && !$past(rst)
                              |-> count == (($past(count) + 1'b1) & MASK));

  // Explicit wrap check from MAX -> 0 on next tick (when not in reset)
  a_wrap: assert property (!rst && !$past(rst) && $past(count) == MASK
                           |-> count == ZERO);

  // No X when not in reset
  a_no_x_when_running: assert property (!rst |-> !$isunknown(count));

  // Coverage: see reset, first increment after release, hit max, wrap
  c_seen_async_clear:  cover property (@(posedge rst) count == ZERO);
  c_first_inc:         cover property ($fell(rst) && count == ONE);
  c_hit_max:           cover property (!rst ##[1:$] count == MASK);
  c_wrap:              cover property (!rst && !$past(rst) && $past(count)==MASK && count==ZERO);

endmodule

bind counter counter_sva #(.n(n)) counter_sva_i (.clk(clk), .rst(rst), .count(count));