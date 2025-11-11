// SVA for nand4_pwrgood: checks functional AND behavior, internal chain correctness,
// X-prop and covers all input combinations. Bind this to the DUT.

module nand4_pwrgood_sva;

  // The checker is bound inside nand4_pwrgood; signals below are referenced in that scope.

  function automatic bit is_pg;
    return (VDD===1'b1 && VSS===1'b0);
  endfunction

  // Sample on any relevant input/power rail edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge VDD or negedge VDD or
    posedge VSS or negedge VSS
  ); endclocking

  // Functional correctness when power is good and inputs are known
  property p_and_func;
    is_pg() && !$isunknown({A,B,C}) |-> ##0 (Y === (A & B & C));
  endproperty
  assert property (p_and_func);

  // Deterministic corners under power-good
  assert property (is_pg() && (A===1 && B===1 && C===1) |-> ##0 (Y===1));
  assert property (is_pg() && (A===0 || B===0 || C===0) |-> ##0 (Y===0));

  // X-propagation: if indeterminate by logic, output must be X
  assert property (is_pg() && $isunknown({A,B,C}) &&
                   !(A===0 || B===0 || C===0) &&
                   !(A===1 && B===1 && C===1) |-> ##0 (Y === 1'bx));

  // No X on Y when rails good and inputs known
  assert property (is_pg() && !$isunknown({A,B,C}) |-> ##0 !$isunknown(Y));

  // Structural equivalence through the gate chain
  assert property (##0 (nand0_out_Y === ~(A & B & C)));
  assert property (##0 (nand1_out_Y === ~nand0_out_Y));
  assert property (##0 (nand2_out_Y === ~nand1_out_Y));
  assert property (##0 (Y === ~nand2_out_Y));

  // Coverage: all input combinations under power-good
  cover property (is_pg() && A===0 && B===0 && C===0 && ##0 Y===0);
  cover property (is_pg() && A===0 && B===0 && C===1 && ##0 Y===0);
  cover property (is_pg() && A===0 && B===1 && C===0 && ##0 Y===0);
  cover property (is_pg() && A===0 && B===1 && C===1 && ##0 Y===0);
  cover property (is_pg() && A===1 && B===0 && C===0 && ##0 Y===0);
  cover property (is_pg() && A===1 && B===0 && C===1 && ##0 Y===0);
  cover property (is_pg() && A===1 && B===1 && C===0 && ##0 Y===0);
  cover property (is_pg() && A===1 && B===1 && C===1 && ##0 Y===1);

  // Output edge coverage under power-good
  cover property (is_pg() && $rose(Y));
  cover property (is_pg() && $fell(Y));

  // Optional rail activity coverage
  cover property ($rose(VDD));
  cover property ($fell(VSS));

endmodule

bind nand4_pwrgood nand4_pwrgood_sva;