// SVA for gated_d_latch
module gated_d_latch_sva (input logic clk, d, en, q);

  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking

  // Functional correctness: update on enable, hold otherwise
  assert property (past_valid && $past(en) |-> q == $past(d));
  assert property (past_valid && !$past(en) |-> q == $past(q));

  // Changes to q only come from enabled clock edge and match d
  assert property (past_valid && (q != $past(q)) |-> $past(en) && q == $past(d));

  // X-propagation guards
  assert property (past_valid |-> !$isunknown(en));
  assert property (past_valid && $past(en) |-> !$isunknown($past(d)) && !$isunknown(q));

  // Coverage: observe hold, update, and both polarities
  cover property (past_valid && !$past(en) && q == $past(q));                  // hold
  cover property (past_valid && $past(en) && q == $past(d));                   // update
  cover property (past_valid && $past(en) && $past(d)==1'b1 && q==1'b1);       // update to 1
  cover property (past_valid && $past(en) && $past(d)==1'b0 && q==1'b0);       // update to 0
  cover property (past_valid && $past(en) && q != $past(q));                   // toggle

endmodule

bind gated_d_latch gated_d_latch_sva sva(.clk(clk), .d(d), .en(en), .q(q));