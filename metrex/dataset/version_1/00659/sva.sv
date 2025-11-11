// SVA for sky130_fd_sc_lp__a2bb2o
// Function: X = (B1 & B2) | ~(A1_N | A2_N)

module sky130_fd_sc_lp__a2bb2o_sva (
  input logic A1_N, A2_N, B1, B2,
  input logic and0_out, nor0_out, or0_out_X,
  input logic X
);
  // Sample on any input edge
  default clocking cb @(
    posedge A1_N or negedge A1_N or
    posedge A2_N or negedge A2_N or
    posedge B1   or negedge B1   or
    posedge B2   or negedge B2
  ); endclocking

  // Functional equivalence
  ap_func:    assert property (X === ((B1 & B2) | ~(A1_N | A2_N)));

  // Gate-level internal consistency
  ap_and:     assert property (and0_out   === (B1 & B2));
  ap_nor:     assert property (nor0_out   === ~(A1_N | A2_N));
  ap_or:      assert property (or0_out_X  === (and0_out | nor0_out));
  ap_buf:     assert property (X          === or0_out_X);

  // Deterministic outcomes with controlling values
  ap_and_c0a: assert property ((B1==1'b0)                |-> and0_out==1'b0);
  ap_and_c0b: assert property ((B2==1'b0)                |-> and0_out==1'b0);
  ap_and_c1:  assert property ((B1==1'b1 && B2==1'b1)    |-> and0_out==1'b1);
  ap_nor_c0:  assert property ((A1_N==1'b1 || A2_N==1'b1)|-> nor0_out==1'b0);
  ap_nor_c1:  assert property ((A1_N==1'b0 && A2_N==1'b0)|-> nor0_out==1'b1);

  // No unknowns on outputs when inputs are all known
  ap_known:   assert property (!$isunknown({A1_N,A2_N,B1,B2}) |-> 
                               !$isunknown({and0_out,nor0_out,or0_out_X,X}));

  // Functional coverage (path activation)
  cp_and_only:  cover property ( and0_out && !nor0_out &&  X);
  cp_nor_only:  cover property (!and0_out &&  nor0_out &&  X);
  cp_both_1:    cover property ( and0_out &&  nor0_out &&  X);
  cp_both_0:    cover property (!and0_out && !nor0_out && !X);

  // Toggle coverage on inputs
  cp_r_A1: cover property ($rose(A1_N));  cp_f_A1: cover property ($fell(A1_N));
  cp_r_A2: cover property ($rose(A2_N));  cp_f_A2: cover property ($fell(A2_N));
  cp_r_B1: cover property ($rose(B1));    cp_f_B1: cover property ($fell(B1));
  cp_r_B2: cover property ($rose(B2));    cp_f_B2: cover property ($fell(B2));
endmodule

// Bind into the DUT (connects to internal nets for thorough checking)
bind sky130_fd_sc_lp__a2bb2o sky130_fd_sc_lp__a2bb2o_sva sva_i (
  .A1_N(A1_N), .A2_N(A2_N), .B1(B1), .B2(B2),
  .and0_out(and0_out), .nor0_out(nor0_out), .or0_out_X(or0_out_X),
  .X(X)
)