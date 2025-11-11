// SVA for nand3. Bind this to the DUT.
// Focus: functional equivalence, 4-state correctness, and full truth-table coverage.

module nand3_sva (input logic A, B, C, Y);

  // Core functional check (4-state aware). Triggers on any change, checks after ##0.
  property p_func;
    @(A or B or C or Y) 1'b1 |-> ##0 (Y === ~(A & B & C));
  endproperty
  assert property (p_func)
    else $error("nand3 func mismatch: A=%b B=%b C=%b Y=%b", A,B,C,Y);

  // Strong corner checks
  property p_any_zero_forces_one;
    @(A or B or C) (A===1'b0 || B===1'b0 || C===1'b0) |-> ##0 (Y===1'b1);
  endproperty
  assert property (p_any_zero_forces_one)
    else $error("nand3: any 0 must force Y=1: A=%b B=%b C=%b Y=%b", A,B,C,Y);

  property p_all_ones_gives_zero;
    @(A or B or C) (A===1'b1 && B===1'b1 && C===1'b1) |-> ##0 (Y===1'b0);
  endproperty
  assert property (p_all_ones_gives_zero)
    else $error("nand3: A=B=C=1 must give Y=0: A=%b B=%b C=%b Y=%b", A,B,C,Y);

  // Unknown propagation: if no input is 0 and at least one is X/Z, Y must be X
  property p_unknown_propagation;
    @(A or B or C)
      (A!==1'b0 && B!==1'b0 && C!==1'b0 && ($isunknown(A) || $isunknown(B) || $isunknown(C)))
      |-> ##0 $isunknown(Y);
  endproperty
  assert property (p_unknown_propagation)
    else $error("nand3: unknowns must propagate when no 0 present: A=%b B=%b C=%b Y=%b", A,B,C,Y);

  // Output should not change without an input change (glitch check)
  property p_no_spurious_y_toggle;
    @(Y) !$stable({A,B,C}) |-> 1'b1; // if Y changes, at least one input changed
  endproperty
  assert property (p_no_spurious_y_toggle)
    else $error("nand3: Y changed without any input change: A=%b B=%b C=%b Y=%b", A,B,C,Y);

  // Truth-table coverage (all 8 known input combos)
  cover property (@(A or B or C) (A===1'b0 && B===1'b0 && C===1'b0) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b0 && B===1'b0 && C===1'b1) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b0 && B===1'b1 && C===1'b0) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b0 && B===1'b1 && C===1'b1) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b1 && B===1'b0 && C===1'b0) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b1 && B===1'b0 && C===1'b1) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b1 && B===1'b1 && C===1'b0) ##0 (Y===1'b1));
  cover property (@(A or B or C) (A===1'b1 && B===1'b1 && C===1'b1) ##0 (Y===1'b0));

  // Additional coverage: Y edges and unknown output
  cover property (@(A or B or C) $rose(Y));
  cover property (@(A or B or C) $fell(Y));
  cover property (@(A or B or C)
                  (A!==1'b0 && B!==1'b0 && C!==1'b0 && ($isunknown(A)||$isunknown(B)||$isunknown(C)))
                  ##0 $isunknown(Y));

endmodule

bind nand3 nand3_sva u_nand3_sva (.A(A), .B(B), .C(C), .Y(Y));