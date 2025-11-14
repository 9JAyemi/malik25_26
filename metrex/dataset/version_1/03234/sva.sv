// SVA for sync2r_1
module sync2r_1_sva (
  input logic clk,
  input logic preset,
  input logic d,
  input logic q,
  input logic q1,
  input logic q2
);

  default clocking cb @(posedge clk); endclocking

  // Async reset clears immediately and holds while asserted
  assert property (@(posedge preset) ##0 (q1==1'b0 && q2==1'b0 && q==1'b0));
  assert property (@(posedge clk) preset |-> (q1==1'b0 && q2==1'b0 && q==1'b0));

  // Pipeline behavior (only when out of reset for required history)
  assert property ((!preset && $past(!preset)) |-> (q1 == $past(d)));
  assert property ((!preset && $past(!preset)) |-> (q2 == $past(q1)));
  assert property ((!preset && $past(!preset) && $past(!preset,2)) |-> (q == $past(d,2)));

  // No glitches: q only changes on clk posedge or preset posedge
  assert property (@(posedge q) ($rose(clk) || $rose(preset)));
  assert property (@(negedge q) ($rose(clk) || $rose(preset)));

  // Basic coverage
  cover property (@(posedge clk) preset ##1 !preset);                 // reset release
  cover property (!preset && $past(!preset,2) && $rose(d) ##2 $rose(q)); // 0->1 propagation
  cover property (!preset && $past(!preset,2) && $fell(d) ##2 $fell(q)); // 1->0 propagation

endmodule

// Bind into DUT to access internals q1/q2
bind sync2r_1 sync2r_1_sva u_sync2r_1_sva (
  .clk   (clk),
  .preset(preset),
  .d     (d),
  .q     (q),
  .q1    (q1),
  .q2    (q2)
);