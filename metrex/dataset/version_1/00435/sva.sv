// SVA bind file for NOR4X0
// Focused, high-quality assertions and coverage

bind NOR4X0 NOR4X0_SVA();

module NOR4X0_SVA;

  // Access DUT signals directly (bound into NOR4X0 scope)
  // IN1, IN2, IN3, IN4, QN, VDD, VSS, n1, n2, n3

  // Sample on any relevant change
  default clocking cb @(IN1 or IN2 or IN3 or IN4 or QN or VDD or VSS or n1 or n2 or n3); endclocking

  function automatic bit pg;
    return (VDD === 1'b1) && (VSS === 1'b0);
  endfunction

  function automatic bit ins_known;
    return !$isunknown({IN1, IN2, IN3, IN4});
  endfunction

  // Power rails must be valid
  assert property (pg)
    else $error("NOR4X0: Power rails invalid (VDD/VSS)");

  // Structural checks on internal NOR chain
  assert property (disable iff (!pg || !ins_known) n1 === ~(IN1 | IN2))
    else $error("NOR4X0: n1 mismatch");

  assert property (disable iff (!pg || !ins_known) n2 === ~(IN3 | IN4))
    else $error("NOR4X0: n2 mismatch");

  assert property (disable iff (!pg || $isunknown({n1,n2})) n3 === ~(n1 | n2))
    else $error("NOR4X0: n3 mismatch");

  assert property (disable iff (!pg) QN === n3)
    else $error("NOR4X0: QN != n3");

  // Functional equivalence: QN == (IN1|IN2) & (IN3|IN4)
  assert property (disable iff (!pg || !ins_known) QN === ((IN1 | IN2) & (IN3 | IN4)))
    else $error("NOR4X0: Functional mismatch");

  // No unintended X on QN when inputs are known and power good
  assert property (disable iff (!pg || !ins_known) !$isunknown(QN))
    else $error("NOR4X0: QN unknown with known inputs");

  // Minimal but meaningful coverage
  cover property (pg && ins_known && (QN === 1'b1));
  cover property (pg && ins_known && (QN === 1'b0));

  // Exercise each input as the sole contributor in its group to make QN=1
  cover property (pg && ins_known && IN1 && !IN2 && IN3 && !IN4 && QN);
  cover property (pg && ins_known && IN1 && !IN2 && IN4 && !IN3 && QN);
  cover property (pg && ins_known && IN2 && !IN1 && IN3 && !IN4 && QN);
  cover property (pg && ins_known && IN2 && !IN1 && IN4 && !IN3 && QN);

  // Toggle coverage
  cover property (pg && ins_known && $rose(QN));
  cover property (pg && ins_known && $fell(QN));
  cover property (pg && ins_known && $rose(IN1));
  cover property (pg && ins_known && $fell(IN1));
  cover property (pg && ins_known && $rose(IN2));
  cover property (pg && ins_known && $fell(IN2));
  cover property (pg && ins_known && $rose(IN3));
  cover property (pg && ins_known && $fell(IN3));
  cover property (pg && ins_known && $rose(IN4));
  cover property (pg && ins_known && $fell(IN4));

endmodule