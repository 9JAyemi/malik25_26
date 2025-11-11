// SVA for d_ff_async_rst_set
// Checks reset/set priority, data capture, output complementarity, and no mid-cycle glitches.
// Includes concise coverage for all behaviors.

module d_ff_async_rst_set_sva (
  input clk,
  input rst,
  input set,
  input d,
  input q,
  input qn
);
  // Track when $past is valid
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Outputs are always complementary
  assert property (@(posedge clk or negedge clk) qn === ~q);

  // Flop update rule (sampled one cycle later due to SVA preponed sampling)
  // q observed at this posedge must equal function of inputs from previous posedge
  assert property (disable iff (!past_valid)
                   q == ( ($past(rst) == 1'b0) ? 1'b0
                       : ($past(set) == 1'b0) ? 1'b1
                       :                       $past(d) ));

  // Reset dominates when both active-low controls are low
  assert property (disable iff (!past_valid)
                   ($past(rst)==1'b0 && $past(set)==1'b0) |-> (q==1'b0));

  // No mid-cycle glitches on outputs (should only change on posedge clk)
  assert property (@(negedge clk) $stable(q) && $stable(qn));

  // No X/Z on outputs after first sampled cycle
  assert property (disable iff (!past_valid) !$isunknown(q) && !$isunknown(qn));

  // Coverage: hit each control path
  cover property (disable iff (!past_valid) ($past(rst)==1'b0) && (q==1'b0));               // reset branch
  cover property (disable iff (!past_valid) ($past(rst)==1'b1 && $past(set)==1'b0) && q);   // set branch
  cover property (disable iff (!past_valid) ($past(rst)==1'b1 && $past(set)==1'b1) &&
                                             (q==$past(d)));                                // data branch

  // Coverage: simultaneous reset and set (reset priority)
  cover property (disable iff (!past_valid) ($past(rst)==1'b0 && $past(set)==1'b0) && (q==1'b0));

  // Coverage: data captures both 0 and 1; observe q toggles via data path
  cover property (disable iff (!past_valid) ($past(rst)&&$past(set)&&$past(d)==1'b0) && (q==1'b0));
  cover property (disable iff (!past_valid) ($past(rst)&&$past(set)&&$past(d)==1'b1) && (q==1'b1));
  cover property (disable iff (!past_valid) ($past(rst)&&$past(set)) && (q != $past(q)));   // q toggled via data
endmodule

// Bind into DUT (comment out if you prefer inline instantiation)
// Assumes hierarchical bind is supported by your tool.
bind d_ff_async_rst_set d_ff_async_rst_set_sva u_d_ff_async_rst_set_sva (
  .clk(clk), .rst(rst), .set(set), .d(d), .q(q), .qn(qn)
);