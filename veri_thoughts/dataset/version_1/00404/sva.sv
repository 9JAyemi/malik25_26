// SVA for d_ff_with_set_clear
module d_ff_with_set_clear_sva (
  input clk,
  input d,
  input set,
  input clear,
  input q
);

  // Clear dominates set (and forces 0 on next state)
  a_clr_dominates: assert property (@(posedge clk)
    $past(clear) |-> q == 1'b0);

  // Set forces 1 on next state when clear is low
  a_set: assert property (@(posedge clk)
    $past(set) && !$past(clear) |-> q == 1'b1);

  // Pass-through when neither control is asserted
  a_pass: assert property (@(posedge clk)
    !$past(set) && !$past(clear) |-> q == $past(d));

  // Knownness: if sampled inputs are known, next q must be known
  a_q_known: assert property (@(posedge clk)
    !$isunknown({$past(clear),$past(set),$past(d)}) |-> !($isunknown(q)));

  // Coverage: exercise all behaviors
  c_clear: cover property (@(posedge clk) $past(clear) |-> q == 1'b0);
  c_set:   cover property (@(posedge clk) $past(set) && !$past(clear) |-> q == 1'b1);
  c_both:  cover property (@(posedge clk) $past(set) && $past(clear) |-> q == 1'b0);
  c_d0:    cover property (@(posedge clk) !$past(set) && !$past(clear) && !$past(d) |-> q == 1'b0);
  c_d1:    cover property (@(posedge clk) !$past(set) && !$past(clear) &&  $past(d) |-> q == 1'b1);

endmodule

bind d_ff_with_set_clear d_ff_with_set_clear_sva
  (.clk(clk), .d(d), .set(set), .clear(clear), .q(q));