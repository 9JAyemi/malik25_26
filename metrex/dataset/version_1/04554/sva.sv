// SVA checker for d_ff_en
module d_ff_en_sva(
  input logic clk, en, te, d,
  input logic enclk,
  input logic q // internal DUT reg passed via bind
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1;

  // Clean inputs at clock
  assert property (disable iff (!past_valid) !$isunknown(en));
  assert property (disable iff (!past_valid) $past(en) |-> !$isunknown($past(d)));

  // enclk mirrors en (1-cycle latency)
  assert property (disable iff (!past_valid) enclk == $past(en));

  // q behavior: capture on en, hold otherwise
  assert property (disable iff (!past_valid) $past(en)  |-> (q == $past(d)));
  assert property (disable iff (!past_valid) !$past(en) |-> (q == $past(q)));

  // enclk changes only on clk edge (no effect from te, no negedge glitches)
  assert property (@(negedge clk) enclk == $past(enclk));
  assert property (@(posedge te)   enclk == $past(enclk));

  // te has no effect on q
  assert property (@(posedge te) q == $past(q));

  // Simple functional coverage
  cover property (past_valid && $rose(enclk));
  cover property (past_valid && $fell(enclk));
  cover property (past_valid && $past(en)  && (q == $past(d)));
  cover property (past_valid && !$past(en) && (q == $past(q)));
  cover property (@(posedge te) 1);

endmodule

// Bind example (place in a tb or a package included in tb)
bind d_ff_en d_ff_en_sva u_d_ff_en_sva(.clk(clk), .en(en), .te(te), .d(d), .enclk(enclk), .q(q));