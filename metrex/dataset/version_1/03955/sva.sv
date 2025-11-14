// SVA for and_gate and and_gate_inst
// Bind these into the DUT; focuses on power-good gating, tie-offs, functional correctness, X-prop, and coverage.

module and_gate_inst_sva (
  input logic A1, A2, B1, C1, VPWR, VGND, VPB, VNB, Y
);
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge C1 or negedge C1 or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge Y   or negedge Y
  ); endclocking

  wire power_good = (VPWR===1'b1 && VGND===1'b0);

  // Tie-offs must be constant when power is good
  assert property (disable iff (!power_good)
    (B1===1'b1 && C1===1'b0 && VPB===1'b0 && VNB===1'b0)
  ) else $error("and_gate_inst: tie-offs incorrect");

  // Functional equivalence (when known)
  assert property (disable iff (!power_good)
    (!$isunknown({A1,A2,B1,C1,Y}) |-> Y === ((A1 & A2) & B1 & !C1))
  ) else $error("and_gate_inst: functional mismatch");

  // Y high implies all inputs enable AND path
  assert property (disable iff (!power_good)
    (Y===1'b1 |-> (A1===1'b1 && A2===1'b1 && B1===1'b1 && C1===1'b0))
  ) else $error("and_gate_inst: Y high without required inputs");

  // No X/Z on Y when inputs are known
  assert property (disable iff (!power_good)
    (!$isunknown({A1,A2,B1,C1}) |-> !$isunknown(Y))
  ) else $error("and_gate_inst: Y unknown while inputs known");

  // No spurious Y toggle without inputs toggling
  assert property (disable iff (!power_good)
    $changed(Y) |-> $changed({A1,A2,B1,C1})
  ) else $error("and_gate_inst: Y toggled without input cause");

  // Coverage: power good and full truth table + Y edges
  cover property (power_good);
  cover property (power_good && A1==0 && A2==0 && Y==0);
  cover property (power_good && A1==0 && A2==1 && Y==0);
  cover property (power_good && A1==1 && A2==0 && Y==0);
  cover property (power_good && A1==1 && A2==1 && Y==1);
  cover property (power_good && $rose(Y));
  cover property (power_good && $fell(Y));
endmodule

module and_gate_sva (
  input logic A1, A2, VPWR, VGND, Y
);
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge Y   or negedge Y
  ); endclocking

  wire power_good = (VPWR===1'b1 && VGND===1'b0);

  // Top-level behavior: AND of A1 and A2 when powered
  assert property (disable iff (!power_good)
    (!$isunknown({A1,A2,Y}) |-> Y === (A1 & A2))
  ) else $error("and_gate (wrapper): Y != A1 & A2 under power_good");

  // Simple activity coverage
  cover property (power_good && ($changed(A1) || $changed(A2)));
endmodule

bind and_gate_inst and_gate_inst_sva u_and_gate_inst_sva (.*);
bind and_gate      and_gate_sva      u_and_gate_sva      (.*);