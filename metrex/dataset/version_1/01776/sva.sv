// SVA for dff_en and dff
// Bind these checkers to the DUTs

module dff_en_sva (input logic clk, d, en, q, q_bar);
  // track first valid cycle for $past()
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking

  // Core functionality: gated DFF behavior
  assert property (disable iff (!past_valid) q == $past(en ? d : q));
  assert property (disable iff (!past_valid) en  |-> (q == $past(d)));
  assert property (disable iff (!past_valid) !en |-> (q == $past(q)));

  // Complement output
  assert property (q_bar == ~q);

  // Known-value checks at sample
  assert property (disable iff (!past_valid) !$isunknown({en, d, q, q_bar}));

  // Functional coverage
  cover property (disable iff (!past_valid) !en ##1 (q == $past(q)));             // hold when disabled
  cover property (disable iff (!past_valid) en && (q != $past(q)));               // update causes change
  cover property (disable iff (!past_valid) en && ($past(d)==0) && (q==1));       // 0->1 toggle
  cover property (disable iff (!past_valid) en && ($past(d)==1) && (q==0));       // 1->0 toggle
endmodule

module dff_sva (input logic clk, d, q, q_bar);
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking

  // Core DFF behavior
  assert property (disable iff (!past_valid) q == $past(d));

  // Complement output
  assert property (q_bar == ~q);

  // Known-value checks at sample
  assert property (disable iff (!past_valid) !$isunknown({d, q, q_bar}));

  // Coverage: any toggle
  cover property (disable iff (!past_valid) q != $past(q));
endmodule

bind dff_en dff_en_sva (.clk(clk), .d(d), .en(en), .q(q), .q_bar(q_bar));
bind dff    dff_sva    (.clk(clk), .d(d),           .q(q), .q_bar(q_bar));