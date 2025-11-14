`ifndef SYNTHESIS
// Assertions for dff_mux
module dff_mux_sva (
  input logic        clk,
  input logic [7:0]  d,
  input logic [2:0]  sel,
  input logic [7:0]  q,
  input logic [7:0]  q_int,
  input logic [7:0]  d_int
);
  default clocking cb @(posedge clk); endclocking

  // Pipeline relations inside dff_mux
  assert property (q_int == $past(d_int));
  assert property (d_int == $past(d));

  // Mux behavior and width effect
  assert property (q[7:1] == '0);
  assert property (q[0] == q_int[3'd7 - sel]);

  // Coverage: exercise all sel values and output activity
  genvar i;
  generate for (i=0;i<8;i++) begin : g_sel_cov
    cover property (sel == i[2:0]);
  end endgenerate
  cover property ($changed(q[0]));
endmodule

bind dff_mux dff_mux_sva u_dff_mux_sva (.*);

// Assertions for top_module
module top_module_sva (
  input logic        clk,
  input logic [7:0]  d,
  input logic [7:0]  q,
  input logic [2:0]  sel,
  input logic [7:0]  d_int
);
  default clocking cb @(posedge clk); endclocking

  // Connectivity and pipeline
  assert property (sel == d[2:0]);
  assert property (d_int == $past(d));

  // End-to-end: 3-cycle latency, reversed index select
  assert property ($past(1'b1,3,1'b0) |-> (q[0] == $past(d,3)[3'd7 - d[2:0]]));

  // Width-mismatch effect at top output
  assert property (q[7:1] == '0);

  // Coverage: all selects seen, latency exercised, both q[0] polarities
  genvar j;
  generate for (j=0;j<8;j++) begin : g_top_sel_cov
    cover property (sel == j[2:0]);
  end endgenerate
  cover property ((d != $past(d)) ##3 $changed(q[0]));
  cover property (q[0] == 1'b1);
  cover property (q[0] == 1'b0);
endmodule

bind top_module top_module_sva u_top_module_sva (.*);
`endif