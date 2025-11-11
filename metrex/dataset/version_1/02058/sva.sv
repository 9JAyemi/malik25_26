// SVA bind module for sky130_fd_sc_ls__nand3
// Focus: functional equivalence, X-prop, change correlation, rails, concise coverage

module sky130_fd_sc_ls__nand3_sva (
  input logic A, B, C,
  input logic Y,
  input logic VPWR, VGND, VPB, VNB
);

  // Functional equivalence (4-state accurate) with zero-delay sampling
  assert property (@(A or B or C or Y) ##0 (Y === ~(A & B & C)));

  // Deterministic (no X/Z on inputs => no X/Z on output and correct value)
  assert property (@(A or B or C or Y) !$isunknown({A,B,C}) |-> ##0 (! $isunknown(Y) && (Y == ~(A & B & C))));

  // Truth table corner cases
  assert property (@(A or B or C) (A===1'b0 || B===1'b0 || C===1'b0) |-> ##0 (Y===1'b1));
  assert property (@(A or B or C) (A===1'b1 && B===1'b1 && C===1'b1) |-> ##0 (Y===1'b0));

  // Required X-propagation when no input is definitively 0
  assert property (@(A or B or C) ($isunknown({A,B,C}) && !(A===1'b0 || B===1'b0 || C===1'b0)) |-> ##0 $isunknown(Y));

  // Change correlation: Y changes iff the boolean function changes
  assert property (@(A or B or C or Y) $changed(~(A & B & C)) |-> ##0 $changed(Y));
  assert property (@(A or B or C or Y) $changed(Y)             |-> ##0 $changed(~(A & B & C)));

  // Rails must be correct constants
  assert property (@(VPWR or VPB or VGND or VNB) (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0));

  // Compact functional coverage
  cover property (@(A or B or C) (A===1 && B===1 && C===1) ##0 (Y===0));  // all-ones case
  cover property (@(A or B or C) (A===0 || B===0 || C===0) ##0 (Y===1)); // any-zero case

  // Observe both output edges
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

  // Each input’s control of Y when the other two are 1
  cover property (@(A) (B===1 && C===1 && $fell(A)) ##0 (Y===1));
  cover property (@(A) (B===1 && C===1 && $rose(A)) ##0 (Y===0));
  cover property (@(B) (A===1 && C===1 && $fell(B)) ##0 (Y===1));
  cover property (@(B) (A===1 && C===1 && $rose(B)) ##0 (Y===0));
  cover property (@(C) (A===1 && B===1 && $fell(C)) ##0 (Y===1));
  cover property (@(C) (A===1 && B===1 && $rose(C)) ##0 (Y===0));

endmodule

bind sky130_fd_sc_ls__nand3 sky130_fd_sc_ls__nand3_sva
  svabind (.*);