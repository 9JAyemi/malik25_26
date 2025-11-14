// SVA for six_input_one_output
module six_input_one_output_sva (
  input A1, input A2,
  input B1, input B2,
  input C1, input C2,
  input Y
);
  // Derived terms
  logic pA, pB, pC;
  logic [1:0] pair_count;
  assign pA = A1 & A2;
  assign pB = B1 & B2;
  assign pC = C1 & C2;
  assign pair_count = {1'b0,pA} + {1'b0,pB} + {1'b0,pC};

  // Use any input/output change as the sampling event
  default clocking cb @ (A1 or A2 or B1 or B2 or C1 or C2 or Y); endclocking

  // Functional equivalence (guarded against Xs on inputs)
  a_equiv: assert property ( !$isunknown({A1,A2,B1,B2,C1,C2}) |-> (Y == (pA | pB | pC)) );

  // Output rises only when some pair newly asserts; output falls only when no pair remains asserted
  a_rise_cause: assert property ( $rose(Y) |-> ($rose(pA) || $rose(pB) || $rose(pC)) );
  a_fall_zero:  assert property ( $fell(Y) |-> (pair_count == 2'd0) );

  // No spurious Y toggle without some input change
  a_no_spurious_toggle: assert property ( ($rose(Y) || $fell(Y)) |-> $changed({A1,A2,B1,B2,C1,C2}) );

  // Coverage: each single pair drives Y high; none; double and triple pairs
  c_A_only: cover property ( pA && !pB && !pC && Y );
  c_B_only: cover property ( !pA && pB && !pC && Y );
  c_C_only: cover property ( !pA && !pB && pC && Y );
  c_none:   cover property ( !pA && !pB && !pC && !Y );
  c_two:    cover property ( (pair_count == 2) && Y );
  c_three:  cover property ( (pair_count == 3) && Y );

  // Coverage: observe Y edges
  c_y_rise: cover property ( $rose(Y) );
  c_y_fall: cover property ( $fell(Y) );
endmodule

// Bind into DUT
bind six_input_one_output six_input_one_output_sva sva_inst (.*);