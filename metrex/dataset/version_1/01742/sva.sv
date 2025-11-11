// SVA for top_module. Concise, high-value checks and coverage.

module top_sva (
  input logic        clk,
  input logic [7:0]  in,
  input logic [7:0]  out_edge,
  input logic        out_not,
  input logic [7:0]  out_func
);
  // Guard for $past
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid)

  // Core functional correctness

  // not_gate: out_not equals bitwise NOT of in[0]
  a_not_equiv: assert property (out_not == ~in[0]);

  // edge_detector: rising-edge detect per bit
  a_edge_eq:   assert property (out_edge == (in & ~ $past(in)));

  // functional_module: gate edge vector with replicated not signal
  a_func_eq:   assert property (out_func == (out_edge & {8{out_not}}));

  // Coverage

  // Per-bit: cover rising edge recognized
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : COV_BITS
      c_rise_seen: cover property (($past(in[i]) == 1'b0) && (in[i] == 1'b1) && out_edge[i]);
    end
  endgenerate

  // Cover not gate toggles and corresponding effect
  c_not_low_gate:  cover property (out_not == 1'b0 && (out_edge != '0) && (out_func == '0));
  c_not_high_pass: cover property (out_not == 1'b1 && (out_edge != '0) && (out_func == out_edge));

  // Cover multiple simultaneous rising edges
  c_multi_rise: cover property ($countones(in & ~ $past(in)) >= 2);

  // Cover both polarities of out_not
  c_not_0: cover property (out_not == 1'b0);
  c_not_1: cover property (out_not == 1'b1);

endmodule

bind top_module top_sva top_sva_i(
  .clk      (clk),
  .in       (in),
  .out_edge (out_edge),
  .out_not  (out_not),
  .out_func (out_func)
);