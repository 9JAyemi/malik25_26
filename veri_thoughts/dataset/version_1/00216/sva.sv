// SVA for counter and top_module
// Focused, high-quality checks and coverage

module counter_sva (
  input clk,
  input reset,
  input up_down,
  input [2:0] q
);
  // Track validity of $past after reset
  bit past_valid;
  always @(posedge clk or posedge reset)
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;

  // Asynchronous reset takes effect immediately and holds during reset
  assert property (@(posedge reset) q == 3'd0);
  assert property (@(posedge clk) reset |-> q == 3'd0);

  // First clock after reset deassert: step from 0 according to direction
  assert property (@(posedge clk) $fell(reset) |-> (up_down ? (q==3'd1) : (q==3'd7)));

  // Up/Down step correctness on every cycle out of reset (mod-8)
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && up_down |=> q == (($past(q)+3'd1) & 3'h7));
  assert property (@(posedge clk) disable iff (reset)
                   past_valid && !up_down |=> q == (($past(q)-3'd1) & 3'h7));

  // No X/Z at sampling
  assert property (@(posedge clk) !$isunknown({reset,up_down,q}));

  // Functional coverage: wraps and both directions
  cover property (@(posedge clk) disable iff (reset)
                  $past(q)==3'd7 && up_down |=> q==3'd0);
  cover property (@(posedge clk) disable iff (reset)
                  $past(q)==3'd0 && !up_down |=> q==3'd7);
  cover property (@(posedge clk) disable iff (reset) up_down ##1 !up_down);
endmodule

module top_module_sva (
  input clk,
  input [2:0] q,
  input [2:0] q_internal
);
  // Top output mirrors internal counter output
  assert property (@(posedge clk) q === q_internal);
  // Top-level output never X/Z at sampling
  assert property (@(posedge clk) !$isunknown(q));
  // Observe reset value at top
  cover property (@(posedge clk) q==3'd0);
endmodule

// Bind checkers
bind counter     counter_sva (.clk(clk), .reset(reset), .up_down(up_down), .q(q));
bind top_module  top_module_sva (.clk(clk), .q(q), .q_internal(q_internal));