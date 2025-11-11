// SVA for sky130_fd_sc_lp__a311oi
// Bind these assertions to the DUT

module sky130_fd_sc_lp__a311oi_sva;

  // Sample on any input transition
  `define A311OI_SAMP @(posedge A1 or negedge A1 or \
                         posedge A2 or negedge A2 or \
                         posedge A3 or negedge A3 or \
                         posedge B1 or negedge B1 or \
                         posedge C1 or negedge C1)

  function automatic bit all_known_5(logic a1,a2,a3,b1,c1);
    return !$isunknown({a1,a2,a3,b1,c1});
  endfunction

  // Functional equivalence when inputs are known
  assert property (`A311OI_SAMP
    all_known_5(A1,A2,A3,B1,C1) |-> (Y == ~((A1 & A2 & A3) | B1 | C1)));

  // Internal net consistency (4-state aware)
  assert property (`A311OI_SAMP
    !$isunknown({A1,A2,A3}) |-> (and0_out == (A1 & A2 & A3)));
  assert property (`A311OI_SAMP
    !$isunknown({and0_out,B1,C1}) |-> (nor0_out_Y == ~(and0_out | B1 | C1)));
  assert property (`A311OI_SAMP (Y === nor0_out_Y));

  // Dominance/controlling values (robust to X/Z where applicable)
  assert property (`A311OI_SAMP (B1 === 1'b1) |-> (Y === 1'b0));
  assert property (`A311OI_SAMP (C1 === 1'b1) |-> (Y === 1'b0));
  assert property (`A311OI_SAMP (B1===1'b0 && C1===1'b0 && A1===1'b1 && A2===1'b1 && A3===1'b1) |-> (Y===1'b0));
  assert property (`A311OI_SAMP (B1===1'b0 && C1===1'b0 && (A1===1'b0 || A2===1'b0 || A3===1'b0)) |-> (Y===1'b1));

  // Key functional coverage
  cover property (`A311OI_SAMP (Y==1'b1));
  cover property (`A311OI_SAMP (Y==1'b0));
  cover property (`A311OI_SAMP (B1==1'b1 && Y==1'b0));
  cover property (`A311OI_SAMP (C1==1'b1 && Y==1'b0));
  cover property (`A311OI_SAMP (B1==1'b0 && C1==1'b0 && A1==1'b1 && A2==1'b1 && A3==1'b1 && Y==1'b0));
  cover property (`A311OI_SAMP (B1==1'b0 && C1==1'b0 && (A1==1'b0 || A2==1'b0 || A3==1'b0) && Y==1'b1));

  // Compact truth-table coverage of all input combinations
  covergroup cg_inputs @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge C1);
    cp: coverpoint {A1,A2,A3,B1,C1} { bins all_vals[] = {[0:31]}; }
  endgroup
  cg_inputs cg_i = new();

  `undef A311OI_SAMP
endmodule

bind sky130_fd_sc_lp__a311oi sky130_fd_sc_lp__a311oi_sva sva_inst();