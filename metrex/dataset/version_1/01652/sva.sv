// SVA for my_module: concise, full functional check + key sanity and coverage

module my_module_sva (
  input logic X,
  input logic A1, A2, A3, B1, B2,
  input logic VPWR, VGND, VPB, VNB
);

  // Functional equivalence (with delta-cycle settle) when inputs are known
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   !$isunknown({A1,A2,A3,B1,B2}) |-> ##0
                   (X == ((A1 & A2 & A3) | (B1 & B2))))
    else $error("X != (A1&A2&A3)|(B1&B2)");

  // No spurious output changes (any X change must be caused by an input change)
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $changed(X) |-> $changed({A1,A2,A3,B1,B2}))
    else $error("X changed without input change");

  // Monotonicity (positive-unate): single-bit rise cannot cause X to fall
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $rose(A1) && !$changed({A2,A3,B1,B2}) |-> ##0 !$fell(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $rose(A2) && !$changed({A1,A3,B1,B2}) |-> ##0 !$fell(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $rose(A3) && !$changed({A1,A2,B1,B2}) |-> ##0 !$fell(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $rose(B1) && !$changed({A1,A2,A3,B2}) |-> ##0 !$fell(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $rose(B2) && !$changed({A1,A2,A3,B1}) |-> ##0 !$fell(X));

  // Monotonicity (positive-unate): single-bit fall cannot cause X to rise
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $fell(A1) && !$changed({A2,A3,B1,B2}) |-> ##0 !$rose(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $fell(A2) && !$changed({A1,A3,B1,B2}) |-> ##0 !$rose(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $fell(A3) && !$changed({A1,A2,B1,B2}) |-> ##0 !$rose(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $fell(B1) && !$changed({A1,A2,A3,B2}) |-> ##0 !$rose(X));
  assert property (@(A1 or A2 or A3 or B1 or B2 or X)
                   $fell(B2) && !$changed({A1,A2,A3,B1}) |-> ##0 !$rose(X));

  // Power integrity (constant supplies)
  assert final (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0)
    else $error("Power pins not at expected constants");

  // Coverage: both product terms, their exclusivity, and both driving X
  cover property (@(A1 or A2 or A3 or B1 or B2 or X)
                  (A1 && A2 && A3 && !(B1 && B2)) ##0 (X == 1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X)
                  (B1 && B2 && !(A1 && A2 && A3)) ##0 (X == 1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X)
                  (A1 && A2 && A3 && B1 && B2) ##0 (X == 1));

  // Coverage: output toggles and each input toggles
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $rose(X));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $fell(X));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $rose(A1)); cover property (@(A1 or A2 or A3 or B1 or B2 or X) $fell(A1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $rose(A2)); cover property (@(A1 or A2 or A3 or B1 or B2 or X) $fell(A2));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $rose(A3)); cover property (@(A1 or A2 or A3 or B1 or B2 or X) $fell(A3));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $rose(B1)); cover property (@(A1 or A2 or A3 or B1 or B2 or X) $fell(B1));
  cover property (@(A1 or A2 or A3 or B1 or B2 or X) $rose(B2)); cover property (@(A1 or A2 or A3 or B1 or B2 or X) $fell(B2));

endmodule

// Bind into all instances of my_module (connects to ports and internal supplies)
bind my_module my_module_sva u_my_module_sva (
  .X(X), .A1(A1), .A2(A2), .A3(A3), .B1(B1), .B2(B2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);