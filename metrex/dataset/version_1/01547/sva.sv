// SVA for dual_edge_ff
module dual_edge_ff_sva (
  input logic clk,
  input logic d,
  input logic q,
  input logic q1,
  input logic q2
);

  // q must mirror q2 (combinational tie)
  assert property (@(posedge clk or negedge clk) q === q2);

  // q1 captures d on each posedge (checked at next posedge)
  assert property (@(posedge clk) 1 |-> (q1 === $past(d)));

  // q2 captures q1 on each negedge (checked at next negedge)
  assert property (@(negedge clk) 1 |-> (q2 === $past(q1)));

  // End-to-end: q (at negedge) equals d from the immediately preceding posedge
  assert property (@(negedge clk) 1 |-> (q === $past(d, 1, posedge clk)));

  // Coverage: transfer both 0 and 1
  cover property (@(posedge clk) d==0 ##1 @(negedge clk) q==0);
  cover property (@(posedge clk) d==1 ##1 @(negedge clk) q==1);

  // Coverage: observe toggling through the pipeline
  cover property (@(posedge clk) d==0 ##1 @(negedge clk) q==0
                  ##1 @(posedge clk) d==1 ##1 @(negedge clk) q==1);
  cover property (@(posedge clk) d==1 ##1 @(negedge clk) q==1
                  ##1 @(posedge clk) d==0 ##1 @(negedge clk) q==0);

endmodule

// Bind into the DUT to access internals q1/q2
bind dual_edge_ff dual_edge_ff_sva u_dual_edge_ff_sva (
  .clk(clk),
  .d(d),
  .q(q),
  .q1(q1),
  .q2(q2)
);