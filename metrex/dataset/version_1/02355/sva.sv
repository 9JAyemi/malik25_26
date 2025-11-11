// SVA checker for d_ff_ce_clr
module d_ff_ce_clr_sva(input logic clk, d, ce, clr, q);

  // Track validity of $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Core next-state functional equivalence (dominant clr, then ce, else hold)
  assert property (disable iff (!past_valid)
    q == ( $past(clr) ? 1'b0
        : ($past(ce)  ? $past(d)
                      : $past(q)) ));

  // Any change in q at a clock edge must be caused by clr or ce
  assert property (disable iff (!past_valid)
    $changed(q) |-> ($past(clr) || $past(ce)));

  // Glitch-free: q only changes on clk rising edge
  assert property ( $changed(q) |-> $rose(clk) );

  // Coverage: clear, load(1), load(0), hold, transitions, and clr+ce priority
  cover property (past_valid && $past(clr) && (q == 1'b0)); // clear
  cover property (past_valid && !$past(clr) && $past(ce) && ($past(d)==1'b1) && (q==1'b1)); // load 1
  cover property (past_valid && !$past(clr) && $past(ce) && ($past(d)==1'b0) && (q==1'b0)); // load 0
  cover property (past_valid && !$past(clr) && !$past(ce) && (q==$past(q))); // hold
  cover property (past_valid && !$past(clr) && $past(ce) && ($past(q)==1'b0) && ($past(d)==1'b1) && (q==1'b1)); // 0->1
  cover property (past_valid && !$past(clr) && $past(ce) && ($past(q)==1'b1) && ($past(d)==1'b0) && (q==1'b0)); // 1->0
  cover property (past_valid && $past(clr) && $past(ce) && (q==1'b0)); // clr dominates ce

endmodule

// Bind into DUT
bind d_ff_ce_clr d_ff_ce_clr_sva u_d_ff_ce_clr_sva(.clk(clk), .d(d), .ce(ce), .clr(clr), .q(q));