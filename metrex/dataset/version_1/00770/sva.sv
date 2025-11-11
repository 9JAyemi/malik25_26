// SVA checker for logic_gate
module logic_gate_sva (
  input logic X,
  input logic A1, A2, B1, B2, C1,
  input logic VPWR, VGND, VPB, VNB
);

  // Convenience expression
  function automatic logic ab_high;
    return (A1 & A2) & (~B1 & ~B2);
  endfunction

  // Power rails must be correct
  assert property (@(VPWR or VPB) ##0 (VPWR === 1'b1 && VPB === 1'b1))
    else $error("logic_gate: VPWR/VPB not 1");
  assert property (@(VGND or VNB) ##0 (VGND === 1'b0 && VNB === 1'b0))
    else $error("logic_gate: VGND/VNB not 0");

  // Inputs and output must be 2-state (no X/Z)
  assert property (@(A1 or A2 or B1 or B2 or C1) !$isunknown({A1,A2,B1,B2,C1}))
    else $error("logic_gate: input X/Z detected");
  assert property (@(X) !$isunknown(X))
    else $error("logic_gate: X is X/Z");

  // Functional equivalence (sampled after delta to avoid race/glitch)
  assert property (@(A1 or A2 or B1 or B2 or C1 or X) ##0
                   (X === (C1 | ab_high())))
    else $error("logic_gate: functional mismatch");

  // Dominance: C1 high must force X high
  assert property (@(posedge C1) ##0 (X === 1'b1))
    else $error("logic_gate: C1 dominance violated");

  // Coverage: exercise key cases
  cover property (@(A1 or A2 or B1 or B2 or C1) (C1==0 && ab_high()) ##0 (X==1)); // AB path
  cover property (@(A1 or A2 or B1 or B2 or C1) (C1==1 && !ab_high()) ##0 (X==1)); // C1 path
  cover property (@(A1 or A2 or B1 or B2 or C1) (C1==0 && !ab_high()) ##0 (X==0)); // both false
  cover property (@(A1 or A2 or B1 or B2 or C1) (C1==1 && ab_high())  ##0 (X==1)); // both true
  cover property (@(posedge X));
  cover property (@(negedge X));

endmodule

// Bind into the DUT
bind logic_gate logic_gate_sva u_logic_gate_sva (
  .X(X),
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);