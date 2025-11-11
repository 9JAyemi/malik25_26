// SVA for xnor2: concise, quality-focused, with functional/power checks and coverage.

module xnor2_sva (
  input A, B, Y, VPWR, VGND, VPB, VNB
);

  logic power_good;
  assign power_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Sample on any relevant change (inputs/power)
  default clocking cb @(A or B or VPWR or VGND or VPB or VNB); endclocking

  // Well/body ties must always be correct
  assert property (VPB === VPWR && VNB === VGND);

  // Functional XNOR when power is good (allow a delta for combinational settle)
  assert property (disable iff (!power_good) 1'b1 |-> ##0 (Y === (A ~^ B)));

  // No spurious output toggles when inputs are stable (under power-good)
  assert property (disable iff (!power_good) $stable({A,B}) |-> $stable(Y));

  // Functional coverage: all input combinations under power-good
  cover property (power_good && (A==0) && (B==0) && (Y==1));
  cover property (power_good && (A==0) && (B==1) && (Y==0));
  cover property (power_good && (A==1) && (B==0) && (Y==0));
  cover property (power_good && (A==1) && (B==1) && (Y==1));

  // Output toggle coverage under power-good
  cover property (power_good && $rose(Y));
  cover property (power_good && $fell(Y));

  // Power-up coverage
  cover property ($rose(power_good));

endmodule

bind xnor2 xnor2_sva sva_xnor2 (
  .A(A), .B(B), .Y(Y), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);