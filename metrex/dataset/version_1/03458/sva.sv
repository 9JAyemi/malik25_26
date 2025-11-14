// SVA for dff_ar (async active-low reset DFF)
`ifndef DFF_AR_SVA
`define DFF_AR_SVA

module dff_ar_sva (input logic clk, rst, d, q);

  // Async reset clears q on assertion and holds it low while rst=0
  assert property (@(negedge rst) 1 |=> q == 0);
  assert property (@(posedge clk) !rst |-> (q == 0));

  // Functional capture: when out of reset, q updates with 1-cycle latency
  assert property (@(posedge clk) disable iff (!rst) 1 |=> (q == $past(d)));

  // Glitch-free: q changes only on clk posedge or reset negedge
  assert property (@(posedge q or negedge q) ($rose(clk) || $fell(rst)));

  // X/Z checks
  assert property (@(posedge clk) !$isunknown({rst, d}));
  assert property (@(posedge clk) disable iff (!rst) !$isunknown(q));

  // Coverage
  cover property (@(negedge rst) 1);                 // reset asserted
  cover property (@(posedge  rst) 1);                 // reset released
  cover property (@(posedge clk) rst ##1 $rose(q));   // q captured 1
  cover property (@(posedge clk) rst ##1 $fell(q));   // q captured 0

endmodule

bind dff_ar dff_ar_sva sva (.clk(clk), .rst(rst), .d(d), .q(q));

`endif