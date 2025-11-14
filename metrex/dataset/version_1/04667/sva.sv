// SVA for t_ff: toggle on T, async active-low reset, X-safe, concise coverage
module t_ff_sva (input clk, reset, t, q);

  // Async reset drives q low immediately and stays low while reset=0
  assert property (@(negedge reset) ##0 (q == 1'b0));
  assert property (@(posedge clk) !reset |-> (q == 1'b0));

  // First clock after reset release: previous q=0, so q == t
  assert property (@(posedge clk) $rose(reset) |-> (q == t));

  // Functional behavior when out of reset: q_next = q_prev ^ t
  assert property (@(posedge clk) disable iff (!reset) $past(reset) |-> (q == ($past(q) ^ t)));

  // Equivalent hold/toggle checks
  assert property (@(posedge clk) disable iff (!reset) !t |-> $stable(q));
  assert property (@(posedge clk) disable iff (!reset) t  |-> (q != $past(q)));

  // X-safety
  assert property (@(posedge clk) disable iff (!reset) !$isunknown(t));
  assert property (@(posedge clk or negedge reset) ##0 !$isunknown(q));

  // Coverage: reset assertion/release, hold, and both toggle directions
  cover  property (@(negedge reset) 1);
  cover  property (@(posedge clk) $rose(reset));
  cover  property (@(posedge clk) disable iff (!reset) $past(reset) && !t && (q == $past(q)));
  cover  property (@(posedge clk) disable iff (!reset) $past(reset) &&  t && ($past(q)==1'b0) && (q==1'b1));
  cover  property (@(posedge clk) disable iff (!reset) $past(reset) &&  t && ($past(q)==1'b1) && (q==1'b0));

endmodule

// Bind into DUT
bind t_ff t_ff_sva t_ff_sva_i(.clk(clk), .reset(reset), .t(t), .q(q));