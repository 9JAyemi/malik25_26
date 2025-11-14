// SVA checker for d_ff_async_reset_set
// Binds to DUT and verifies the implemented behavior concisely.

module d_ff_async_reset_set_sva (
  input logic CLK,
  input logic D,
  input logic Reset,
  input logic Set,
  input logic Q
);
  // Track when $past() is valid
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  default clocking cb @(posedge CLK); endclocking

  // Golden functional check (matches RTL: Q <= (Set | (~Reset & ~Set & D)) ^ Q;)
  // q(t) equals expr evaluated at t-1 (standard $past(expr) check for flops).
  assert property (past_valid |-> Q == $past( (Set || (!Reset && !Set && D)) ^ Q ));

  // Key behavioral checks derived from the logic (using t-1 controls):
  // Set causes toggle irrespective of Reset/D.
  assert property (past_valid && $past(Set) |-> Q != $past(Q));

  // If Reset=1 and Set=0, hold.
  assert property (past_valid && $past(Reset) && !$past(Set) |-> Q == $past(Q));

  // If Reset=0, Set=0, D=1 => toggle.
  assert property (past_valid && $past(!Reset && !Set && D) |-> Q != $past(Q));

  // If Reset=0, Set=0, D=0 => hold.
  assert property (past_valid && $past(!Reset && !Set && !D) |-> Q == $past(Q));

  // No X on Q after first cycle.
  assert property (past_valid |-> !$isunknown(Q));

  // Coverage: hit all control paths and both toggle directions.
  cover property (past_valid && $past(Set));                             // Toggle via Set
  cover property (past_valid && $past(Reset) && !$past(Set));            // Hold via Reset
  cover property (past_valid && $past(!Reset && !Set && D));             // Toggle via D
  cover property (past_valid && $past(!Reset && !Set && !D));            // Hold via D=0
  cover property (past_valid && $past(Q)==1'b0 ##1 Q==1'b1);             // 0->1 edge
  cover property (past_valid && $past(Q)==1'b1 ##1 Q==1'b0);             // 1->0 edge

endmodule

// Bind into the DUT
bind d_ff_async_reset_set d_ff_async_reset_set_sva sva_i (.*);