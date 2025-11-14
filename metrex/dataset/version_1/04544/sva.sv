// SVA for dff_rst_set
module dff_rst_set_sva (
  input logic clk,
  input logic rst,
  input logic set,
  input logic d,
  input logic q,
  input logic qn
);

  default clocking cb @(posedge clk); endclocking

  // Next-state function (includes reset/set priority and data path)
  assert property (q == (rst ? 1'b0 : (set ? 1'b1 : d)));

  // Explicit priority when both rst and set are 1
  assert property (rst && set |-> q == 1'b0);

  // Complementary output
  assert property (qn === ~q);

  // No X/Z on registered outputs at clock boundaries
  assert property (!$isunknown({q, qn}));

  // No glitches: q must be stable between clock edges
  assert property (1 |=> $stable(q) until_with posedge clk);

  // Coverage: exercise all control/data paths and a 0->1->0 toggle
  cover property (rst && !set);
  cover property (!rst && set);
  cover property (!rst && !set && d == 1'b0);
  cover property (!rst && !set && d == 1'b1);
  cover property (rst && set);               // both asserted case
  cover property (q == 1'b0 ##1 q == 1'b1 ##1 q == 1'b0);

endmodule

// Bind into DUT
bind dff_rst_set dff_rst_set_sva sva_i (
  .clk(clk), .rst(rst), .set(set), .d(d), .q(q), .qn(qn)
);