// SVA checker for Multiplexer_AC__parameterized94
module Multiplexer_AC__parameterized94_sva
  (input  logic       clk,
   input  logic       rst_n,
   input  logic       ctrl,
   input  logic [0:0] D0,
   input  logic [0:0] D1,
   input  logic [0:0] S);

  // Immediate combinational check (glitch-sensitive)
  always_comb begin
    assert (S === (ctrl ? D1 : D0))
      else $error("MUX func mismatch: ctrl=%0b D0=%0b D1=%0b S=%0b", ctrl, D0, D1, S);
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Cleanliness (no X/Z after reset)
  ap_no_x_ctrl: assert property (!$isunknown(ctrl));
  ap_no_x_in  : assert property (!$isunknown({D0,D1}));
  ap_no_x_out : assert property (!$isunknown(S));

  // Functional correctness
  ap_func  : assert property (S == (ctrl ? D1 : D0));
  ap_sel0  : assert property (!ctrl |-> (S == D0));
  ap_sel1  : assert property ( ctrl |-> (S == D1));
  ap_eq_in : assert property ((D0 == D1) |-> (S == D0));

  // Stability: if select and inputs hold, output holds
  ap_stable: assert property ($stable({ctrl,D0,D1}) |-> $stable(S));

  // Coverage
  cp_sel0        : cover property (!ctrl && (S == D0));
  cp_sel1        : cover property ( ctrl && (S == D1));
  cp_toggle_0_to_1: cover property (!ctrl ##1 ctrl);
  cp_toggle_1_to_0: cover property ( ctrl ##1 !ctrl);
  cp_equal_inputs: cover property ((D0 == D1) && (S == D0));
endmodule

// Example bind (hook clk/rst_n from your environment)
// bind Multiplexer_AC__parameterized94 Multiplexer_AC__parameterized94_sva u_mux_sva (clk, rst_n, ctrl, D0, D1, S);