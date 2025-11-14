// SVA for comparator. Bind this to the DUT.
// Ensures 1-cycle latency behavior and correct encoding, with concise coverage.

module comparator_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [1:0]  OUT
);

  // Guard first cycle (no reset in DUT)
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // No unknowns / illegal code after pipeline is initialized
  assert property (past_valid |-> !$isunknown(OUT));
  assert property (past_valid |-> OUT != 2'b00);

  // Functional mapping: previous A,B decide current OUT (both directions)
  assert property (past_valid |-> (($past(A) >  $past(B)) -> (OUT == 2'b01)));
  assert property (past_valid |-> (($past(A) <  $past(B)) -> (OUT == 2'b10)));
  assert property (past_valid |-> (($past(A) == $past(B)) -> (OUT == 2'b11)));

  assert property (past_valid |-> ((OUT == 2'b01) -> ($past(A) >  $past(B))));
  assert property (past_valid |-> ((OUT == 2'b10) -> ($past(A) <  $past(B))));
  assert property (past_valid |-> ((OUT == 2'b11) -> ($past(A) == $past(B))));

  // Basic functional coverage (cause-effect and transitions)
  cover property (past_valid && ($past(A) >  $past(B)) && (OUT == 2'b01));
  cover property (past_valid && ($past(A) <  $past(B)) && (OUT == 2'b10));
  cover property (past_valid && ($past(A) == $past(B)) && (OUT == 2'b11));

  cover property (past_valid && (OUT == 2'b01) ##1 (OUT == 2'b10));
  cover property (past_valid && (OUT == 2'b10) ##1 (OUT == 2'b01));
  cover property (past_valid && (OUT == 2'b11) ##1 (OUT != 2'b11));

endmodule

// Bind to DUT (use wildcard to hook up by name)
bind comparator comparator_sva u_comparator_sva (.*);