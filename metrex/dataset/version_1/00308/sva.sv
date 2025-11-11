// SVA checker for counter. Bind to the DUT to see internal "count".
module counter_sva(input logic clk, reset, in, p, input logic [2:0] count);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset clears immediately (after NBA in same timestep)
  assert property (@(posedge reset) ##0 (count == 3'd0));

  // While reset is held, counter is 0
  assert property (reset |-> (count == 3'd0));

  // No X on key signals when not in reset
  assert property (disable iff (reset) !$isunknown({p, count, in}));

  // Output correctness
  assert property (p == (count == 3'd5));

  // Functional updates
  // If in==0, next count is 0
  assert property (disable iff (reset) (!in) |=> (count == 3'd0));

  // If in==1, next count increments with wrap at 7->0
  assert property (disable iff (reset)
                   in |=> (count == (($past(count) == 3'd7) ? 3'd0 : ($past(count) + 3'd1))));

  // Liveness: from count==0 and 5 consecutive in==1 cycles, p must assert
  assert property (disable iff (reset)
                   (count == 3'd0 && in) ##1 in[*4] |=> p);

  // When in stays 0, count stays at 0 after the first clear
  assert property (disable iff (reset)
                   (!in && $past(!in)) |=> (count == 3'd0) && $stable(count));

  // Coverage
  cover property (@(posedge reset) 1); // reset seen
  cover property (disable iff (reset)
                  (count == 3'd0 && in) ##1 in[*4] ##1 p); // p assertion path
  cover property (disable iff (reset)
                  (count == 3'd7 && in) |=> (count == 3'd0)); // wrap-around

endmodule

bind counter counter_sva u_counter_sva (.clk(clk), .reset(reset), .in(in), .p(p), .count(count));