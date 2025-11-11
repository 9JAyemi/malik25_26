// SVA for Multiplexer (concise, high-quality)
// Provide a sampling clock from your environment. Bind as shown below.

module Multiplexer_sva #(parameter WIDTH = 1) (
  input  logic                   clk,
  input  logic                   ctrl,
  input  logic [WIDTH-1:0]       D0,
  input  logic [WIDTH-1:0]       D1,
  input  logic [WIDTH-1:0]       S
);

  default clocking cb @(posedge clk); endclocking

  // Functional correctness with X-merge semantics (flags X-optimism)
  ap_func:        assert property (S === (ctrl ? D1 : D0));

  // Selected-input correctness and no-X when select and selected input are known
  ap_sel0_no_x:   assert property ((ctrl === 1'b0 && !$isunknown(D0)) |-> (S == D0 && !$isunknown(S)));
  ap_sel1_no_x:   assert property ((ctrl === 1'b1 && !$isunknown(D1)) |-> (S == D1 && !$isunknown(S)));

  // Output stability when all inputs stable
  ap_stable:      assert property ($stable({ctrl, D0, D1}) |-> $stable(S));

  // Any S change must be caused by a change on ctrl/D0/D1
  ap_change_cause: assert property ($changed(S) |-> ($changed(ctrl) || $changed(D0) || $changed(D1)));

  // Coverage: both selections, toggles, equal/different inputs, unknown select
  cp_sel0:        cover property (ctrl === 1'b0);
  cp_sel1:        cover property (ctrl === 1'b1);
  cp_tog_01:      cover property (ctrl === 1'b0 ##1 ctrl === 1'b1);
  cp_tog_10:      cover property (ctrl === 1'b1 ##1 ctrl === 1'b0);
  cp_eq_inputs:   cover property (D0 === D1);
  cp_ne_inputs:   cover property (D0 !== D1);
  cp_x_ctrl:      cover property ($isunknown(ctrl));
  cp_x_risky:     cover property ($isunknown(ctrl) && (D0 !== D1)); // exercises X-optimism hazard

endmodule

// Example bind (provide a clock from your TB/environment):
// bind Multiplexer Multiplexer_sva #(.WIDTH(WIDTH)) mux_sva ( .clk(tb_clk), .ctrl(ctrl), .D0(D0), .D1(D1), .S(S) );