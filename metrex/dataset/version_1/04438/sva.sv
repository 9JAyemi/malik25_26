// SVA for dff_ce_clr
module dff_ce_clr_sva(input logic clk, clr, ce, d, q);

  default clocking cb @(posedge clk); endclocking

  // X-checks
  assert property (!$isunknown({clr, ce, d}));
  assert property ($past(1'b1) |-> !$isunknown(q));

  // Functional correctness
  assert property ($past(clr) |-> (q == 1'b0));                         // clear wins
  assert property ($past(!clr && ce) |-> (q == $past(d)));               // load when enabled
  assert property ($past(!clr && !ce) |-> (q == $past(q)));              // hold when disabled
  assert property ($changed(q) |-> $past(clr || ce));                    // q changes only if clr/ce was set

  // Coverage
  cover property ($past(clr) && (q == 1'b0));                            // clear observed
  cover property ($past(!clr && ce && d) && (q == 1'b1));                // load 1
  cover property ($past(!clr && ce && !d) && (q == 1'b0));               // load 0
  cover property ($past(!clr && !ce) && (q == $past(q)));                // hold
  cover property ($past(clr && ce) && (q == 1'b0));                      // clr priority over ce

endmodule

bind dff_ce_clr dff_ce_clr_sva sva_inst(.clk(clk), .clr(clr), .ce(ce), .d(d), .q(q));