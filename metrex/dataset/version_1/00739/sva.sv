// SVA for mux4to1. Bind this module to the DUT and connect a sampling clock and reset.
// The assertions are concurrent SVA, sampling on posedge clk.

module mux4to1_sva (
  input logic clk,
  input logic rst_n,
  input logic A, B, C, D, S0, S1,
  input logic Y
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional truth-table checks (4-state accurate, allow ##0 for combinational settle)
  a_sel_00: assert property ( (S1===1'b0 && S0===1'b0) |-> ##0 (Y === A) );
  a_sel_01: assert property ( (S1===1'b0 && S0===1'b1) |-> ##0 (Y === B) );
  a_sel_10: assert property ( (S1===1'b1 && S0===1'b0) |-> ##0 (Y === C) );
  a_sel_11: assert property ( (S1===1'b1 && S0===1'b1) |-> ##0 (Y === D) );

  // No X propagation when all driving inputs are known
  a_no_x_when_known: assert property (
    !$isunknown({S1,S0,A,B,C,D}) |-> ##0 !$isunknown(Y)
  );

  // Coverage: hit each select case and confirm routed input reaches Y
  c_sel_00: cover property ( (S1===1'b0 && S0===1'b0) ##0 (Y === A) );
  c_sel_01: cover property ( (S1===1'b0 && S0===1'b1) ##0 (Y === B) );
  c_sel_10: cover property ( (S1===1'b1 && S0===1'b0) ##0 (Y === C) );
  c_sel_11: cover property ( (S1===1'b1 && S0===1'b1) ##0 (Y === D) );

endmodule

// Example bind (provide clk/rst_n from your environment):
// bind mux4to1 mux4to1_sva u_mux4to1_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));