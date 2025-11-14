// SVA for nand2, and2, and top nand_gate. Bind these to the DUT.

module nand2_sva (input logic A, B, Y);
  default clocking cb @ (A or B or Y); endclocking

  // Functional equivalence and 4-state correctness
  assert property (1'b1 |-> ##0 (Y === ~(A & B)));

  // Knownness when inputs are known; output never Z
  assert property (!$isunknown({A,B}) |-> !$isunknown(Y));
  assert property (1'b1 |-> ##0 (Y !== 1'bz));

  // Coverage: all input combos and Y edges
  cover property (A==0 && B==0 && Y==1);
  cover property (A==0 && B==1 && Y==1);
  cover property (A==1 && B==0 && Y==1);
  cover property (A==1 && B==1 && Y==0);
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

module and2_sva (input logic A, B, Y);
  default clocking cb @ (A or B or Y); endclocking

  assert property (1'b1 |-> ##0 (Y === (A & B)));
  assert property (!$isunknown({A,B}) |-> !$isunknown(Y));
  assert property (1'b1 |-> ##0 (Y !== 1'bz));

  cover property (A==0 && B==0 && Y==0);
  cover property (A==0 && B==1 && Y==0);
  cover property (A==1 && B==0 && Y==0);
  cover property (A==1 && B==1 && Y==1);
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

module nand_gate_sva (input logic A, B, VPWR, VGND, KAPWR, Y);
  default clocking cb @ (A or B or KAPWR or VPWR or VGND or Y); endclocking

  // Power pin sanity (since not functionally used here)
  assert property (VPWR === 1'b1);
  assert property (VGND === 1'b0);

  // Output never Z
  assert property (1'b1 |-> ##0 (Y !== 1'bz));

  // Functional equivalence (4-state)
  assert property (1'b1 |-> ##0 (Y === ((~(A & B)) & KAPWR)));

  // Gating behavior
  assert property ((KAPWR === 1'b0) |-> ##0 (Y === 1'b0));
  assert property ((KAPWR === 1'b1) |-> ##0 (Y === ~(A & B)));

  // Knownness and X-propagation rules
  assert property (!$isunknown({A,B,KAPWR}) |-> !$isunknown(Y));
  assert property ((KAPWR === 1'b1) && ($isunknown(A) || $isunknown(B)) |-> $isunknown(Y));
  assert property ((KAPWR === 1'b0) && ($isunknown(A) || $isunknown(B)) |-> (Y === 1'b0));

  // Coverage: all 8 input combinations and Y edges
  cover property (KAPWR==0 && A==0 && B==0 && Y==0);
  cover property (KAPWR==0 && A==0 && B==1 && Y==0);
  cover property (KAPWR==0 && A==1 && B==0 && Y==0);
  cover property (KAPWR==0 && A==1 && B==1 && Y==0);
  cover property (KAPWR==1 && A==0 && B==0 && Y==1);
  cover property (KAPWR==1 && A==0 && B==1 && Y==1);
  cover property (KAPWR==1 && A==1 && B==0 && Y==1);
  cover property (KAPWR==1 && A==1 && B==1 && Y==0);

  cover property ($rose(Y));
  cover property ($fell(Y));

  // Coverage of masked vs propagated X
  cover property ($isunknown({A,B}) && (KAPWR==0) && (Y==0));
  cover property ($isunknown({A,B}) && (KAPWR==1) && $isunknown(Y));
endmodule

bind nand2     nand2_sva     u_nand2_sva     (.*);
bind and2      and2_sva      u_and2_sva      (.*);
bind nand_gate nand_gate_sva u_nand_gate_sva (.*);