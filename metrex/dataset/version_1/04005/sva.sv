// SVA for sky130_fd_sc_lp__a221o: X = (A1&A2) | (B1&B2) | C1, power-aware

module sky130_fd_sc_lp__a221o_sva (
  input X,
  input A1, A2, B1, B2, C1,
  input VPWR, VGND, VPB, VNB
);

  // Power-good definition (4-state exact)
  wire pwr_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Combinational sampling event on any relevant change
  event comb_ev;
  always @(A1 or A2 or B1 or B2 or C1 or VPWR or VGND or VPB or VNB or X) -> comb_ev;

  // Functional equivalence (4-state)
  assert property (@(comb_ev) disable iff (!pwr_good)
                   X === ((A1 & A2) | (B1 & B2) | C1));

  // No X on output if inputs are known (under good power)
  assert property (@(comb_ev) disable iff (!pwr_good)
                   !$isunknown({A1,A2,B1,B2,C1}) |-> !$isunknown(X));

  // Dominance checks
  assert property (@(comb_ev) disable iff (!pwr_good) C1 |-> (X==1'b1));
  assert property (@(comb_ev) disable iff (!pwr_good) (A1 & A2) |-> (X==1'b1));
  assert property (@(comb_ev) disable iff (!pwr_good) (B1 & B2) |-> (X==1'b1));

  // Zero condition when no term is true
  assert property (@(comb_ev) disable iff (!pwr_good)
                   !C1 && !(A1 & A2) && !(B1 & B2) |-> (X==1'b0));

  // Coverage: output toggles
  cover property (@(comb_ev) pwr_good && $rose(X));
  cover property (@(comb_ev) pwr_good && $fell(X));

  // Coverage: each OR term solely controls X
  cover property (@(comb_ev) pwr_good && C1 && X);
  cover property (@(comb_ev) pwr_good && !C1 && A1 && A2 && !(B1 & B2) && X);
  cover property (@(comb_ev) pwr_good && !C1 && B1 && B2 && !(A1 & A2) && X);
  // Coverage: none true -> X low
  cover property (@(comb_ev) pwr_good && !C1 && !(A1 & A2) && !(B1 & B2) && !X);

endmodule

bind sky130_fd_sc_lp__a221o sky130_fd_sc_lp__a221o_sva sva_i (.*);