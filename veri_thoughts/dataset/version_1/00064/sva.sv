// SVA for and_gate
// Focus: functional equivalence, unknown handling, unused-pin independence, and concise coverage.

module and_gate_sva #(parameter bit CHECK_RAILS = 1) (
  input logic A1, A2, B1,
  input logic VPWR, VGND, VPB, VNB,
  input logic X
);
  // Sample on any relevant change
  default clocking cb @(A1 or A2 or B1 or VPWR or VGND or VPB or VNB or X); endclocking

  // Functional equivalence (4-state accurate)
  assert property (X === (A1 & A2 & B1 & VPWR))
    else $error("and_gate: X != A1&A2&B1&VPWR (4-state)");

  // If inputs known, output must be known
  assert property ((!$isunknown({A1,A2,B1,VPWR})) |-> !$isunknown(X))
    else $error("and_gate: X unknown while inputs known");

  // Explicit 1/0 implications (clarity)
  assert property ((A1 && A2 && B1 && VPWR) |-> X===1'b1);
  assert property ((!$isunknown({A1,A2,B1,VPWR}) && (!A1 || !A2 || !B1 || !VPWR)) |-> X===1'b0);

  // Unused pins must not affect X
  assert property ($changed(VGND) && $stable({A1,A2,B1,VPWR,VPB,VNB}) |-> $stable(X));
  assert property ($changed(VPB)  && $stable({A1,A2,B1,VPWR,VGND,VNB}) |-> $stable(X));
  assert property ($changed(VNB)  && $stable({A1,A2,B1,VPWR,VGND,VPB}) |-> $stable(X));

  // Optional rail checks
  if (CHECK_RAILS) begin
    assert property (!$isunknown({VPWR,VGND,VPB,VNB}))
      else $error("and_gate: rail/bias pin X/Z");
    assert property ((VPWR===1'b1) |-> (VGND===1'b0 && VPB===1'b1 && VNB===1'b0))
      else $error("and_gate: illegal rail/bias when powered");
  end

  // Coverage: output states and edges
  cover property (X===1'b1);
  cover property (X===1'b0);
  cover property ($rose(X));
  cover property ($fell(X));

  // Coverage: key input combinations
  cover property (A1 && A2 && B1 && VPWR);          // all ones
  cover property ((!A1) &&  A2 &&  B1 &&  VPWR);    // single zero on A1
  cover property ( A1 && (!A2) &&  B1 &&  VPWR);    // single zero on A2
  cover property ( A1 &&  A2 && (!B1) &&  VPWR);    // single zero on B1
  cover property ( A1 &&  A2 &&  B1 && (!VPWR));    // VPWR low

  // Coverage: toggles
  cover property ($rose(A1));  cover property ($fell(A1));
  cover property ($rose(A2));  cover property ($fell(A2));
  cover property ($rose(B1));  cover property ($fell(B1));
  cover property ($rose(VPWR));cover property ($fell(VPWR));
  cover property ($rose(VGND));cover property ($fell(VGND));
  cover property ($rose(VPB)); cover property ($fell(VPB));
  cover property ($rose(VNB)); cover property ($fell(VNB));
endmodule

// Bind into DUT
bind and_gate and_gate_sva sva_i (.*);