// SVA for top_module
module top_module_sva (
  input clk,
  input reset,
  input [3:0] a,
  input [3:0] b,
  input ctrl,
  input [3:0] out_adder,
  input [2:0] out_comparator,
  input [3:0] adder_output,
  input [2:0] comparator_output,
  input [3:0] mux_output
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // No X/Z propagation when inputs known
  ap_no_x: assert property (!$isunknown({a,b,ctrl})) |-> !$isunknown({adder_output, comparator_output, mux_output, out_adder, out_comparator});

  // Adder correctness (4-bit wrap)
  ap_adder:  assert property (adder_output == ((a + b) & 4'hF));

  // Comparator correctness (one-hot and mapping)
  ap_cmp_1h: assert property ($onehot(comparator_output));
  ap_cmp_gt: assert property ((a > b)  <-> comparator_output[2]);
  ap_cmp_eq: assert property ((a == b) <-> comparator_output[1]);
  ap_cmp_lt: assert property ((a < b)  <-> comparator_output[0]);

  // Mux correctness
  ap_mux:    assert property (mux_output == (ctrl ? {1'b0, comparator_output} : adder_output));

  // Output wiring
  ap_o_map0: assert property (out_adder == mux_output);
  ap_o_map1: assert property (out_comparator == mux_output[2:0]);

  // End-to-end behavior from inputs
  ap_e2e_c0: assert property ((!ctrl) |-> (out_adder == ((a + b) & 4'hF)
                                        && out_comparator == (((a + b) & 4'hF)[2:0])));
  ap_e2e_c1: assert property (( ctrl) |-> (out_adder == {1'b0, ((a>b)?3'b100 : (a==b)?3'b010 : 3'b001)}
                                        && out_comparator ==      ((a>b)?3'b100 : (a==b)?3'b010 : 3'b001)));

  // Coverage
  cv_ctrl0:      cover property (!ctrl);
  cv_ctrl1:      cover property ( ctrl);
  cv_ctrl_tgl01: cover property (!ctrl ##1 ctrl);
  cv_ctrl_tgl10: cover property ( ctrl ##1 !ctrl);

  cv_cmp_gt:     cover property (a > b);
  cv_cmp_eq:     cover property (a == b);
  cv_cmp_lt:     cover property (a < b);

  // Adder overflow wrap (sum < a implies carry out)
  cv_add_ovf:    cover property (adder_output < a);

  // Useful crosses
  cv_sel_cmp_gt: cover property (ctrl && (a > b));
  cv_sel_cmp_eq: cover property (ctrl && (a == b));
  cv_sel_cmp_lt: cover property (ctrl && (a < b));

endmodule

bind top_module top_module_sva sva_i (.*);