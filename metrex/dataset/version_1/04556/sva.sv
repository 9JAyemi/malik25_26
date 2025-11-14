// SVA for dff_chain and top_module
// Focused, concise checks and coverage

`ifndef DFF_CHAIN_TOP_SVA
`define DFF_CHAIN_TOP_SVA

module dff_chain_sva #(parameter WIDTH=8)
(
  input logic               clk,
  input logic               reset,
  input logic [WIDTH-1:0]   d,
  input logic [WIDTH-1:0]   q
);
  default clocking cb @(posedge clk); endclocking

  // Functional checks
  ap_reset_next: assert property (reset |=> q == 'h34);
  ap_reset_hold: assert property (!$initstate && $past(reset) |-> q == 'h34);
  ap_capture:    assert property (!$initstate && !reset |=> q == $past(d));

  // Sanity/knownness
  ap_q_known: assert property (!$initstate |-> !$isunknown(q));
  ap_d_known: assert property (!$initstate |-> !$isunknown(d));

  // Basic coverage
  cp_reset:      cover property (reset ##1 q == 'h34);
  cp_cap_change: cover property (!reset && $changed(d) ##1 q == $past(d));

  // Per-bit toggle coverage (both directions)
  genvar i;
  generate
    for (i=0; i<WIDTH; i++) begin : BITCOV
      cover property (!reset && $rose(d[i]) ##1 $rose(q[i]));
      cover property (!reset && $fell(d[i]) ##1 $fell(q[i]));
    end
  endgenerate
endmodule

module top_module_sva
(
  input logic       clk,
  input logic       reset,
  input logic [7:0] d,
  input logic [7:0] q
);
  default clocking @(posedge clk); endclocking

  // Connectivity and end-to-end behavior
  ap_conn:      assert property (1'b1 |-> q == dff_inst.q);
  ap_top_lat:   assert property (!$initstate && !reset |=> q == $past(d));
  ap_top_reset: assert property (reset |=> q == 8'h34);

  // Simple end-to-end coverage
  cp_e2e: cover property (!reset && $changed(d) ##1 q == $past(d));
endmodule

// Binds
bind dff_chain  dff_chain_sva #(.WIDTH(8)) dff_chain_sva_i (.clk(clk), .reset(reset), .d(d), .q(q));
bind top_module top_module_sva                top_module_sva_i (.clk(clk), .reset(reset), .d(d), .q(q));

`endif