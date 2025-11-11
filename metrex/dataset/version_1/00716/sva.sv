// SVA for d_ff_pre: D flip-flop with async preset (active-high)
module d_ff_pre_sva (input logic D, C, PRE, Q);

  // Async PRE forces Q=1 immediately and dominates on C edges
  assert property (@(posedge PRE) ##0 (Q == 1'b1));
  assert property (@(posedge C) PRE |-> ##0 (Q == 1'b1));

  // Synchronous capture on C when PRE=0
  assert property (@(posedge C) !PRE |-> ##0 (Q == $sampled(D)));

  // PRE deassertion does not change Q (remains 1 at that instant)
  assert property (@(negedge PRE) ##0 (Q == 1'b1));

  // Sanity: no X on controls at edges; D known when captured; Q known after update
  assert property (@(posedge PRE) !$isunknown(PRE));
  assert property (@(posedge C)  !$isunknown(C));
  assert property (@(posedge C)  !PRE |-> !$isunknown($sampled(D)));
  assert property (@(posedge C or posedge PRE) ##0 !$isunknown(Q));

  // Functional coverage
  cover property (@(posedge PRE) 1);              // async preset seen
  cover property (@(posedge C) !PRE && ($sampled(D) == 1'b0)); // capture 0
  cover property (@(posedge C) !PRE && ($sampled(D) == 1'b1)); // capture 1
  cover property (@(posedge C) $rose(PRE));       // simultaneous C and PRE rise

endmodule

bind d_ff_pre d_ff_pre_sva dut_sva (.*);