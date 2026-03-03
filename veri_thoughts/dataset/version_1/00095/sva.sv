// SVA for counter: 2-bit up counter with synchronous reset and wrap at 3->0
module counter_sva(input logic clk, reset, input logic [1:0] count);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Sanity
  assert property (!$isunknown({reset, count}));

  // Synchronous reset forces zero (every cycle asserted)
  assert property (reset |-> count == 2'b00);
  assert property (past_valid && reset && $past(reset) |-> count == 2'b00);

  // Next-state behavior when not in/reset (prev and curr cycles both not reset)
  assert property (past_valid && !reset && !$past(reset) && ($past(count) != 2'b11)
                   |-> count == $past(count) + 2'b01);
  assert property (past_valid && !reset && !$past(reset) && ($past(count) == 2'b11)
                   |-> count == 2'b00);

  // Reset release behavior (last cycle reset=1, now 0) -> increment from 0 to 1
  assert property (past_valid && $fell(reset) |-> count == 2'b01);

  // Periodicity: after 4 reset-free cycles, value repeats
  assert property (past_valid &&
                   !reset && !$past(reset,1) && !$past(reset,2) && !$past(reset,3) && !$past(reset,4)
                   |-> count == $past(count,4));

  // Functional coverage
  cover property (count == 2'b00);
  cover property (count == 2'b01);
  cover property (count == 2'b10);
  cover property (count == 2'b11);
  cover property (disable iff (reset))
                 (count==2'b00 ##1 count==2'b01 ##1 count==2'b10 ##1 count==2'b11 ##1 count==2'b00);
  cover property ($fell(reset));
endmodule

// Bind into DUT
bind counter counter_sva counter_sva_i(.clk(clk), .reset(reset), .count(count));