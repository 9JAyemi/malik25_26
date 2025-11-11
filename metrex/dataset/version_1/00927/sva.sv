// SVA for sky130_fd_sc_ms__a2111o
// Function: X = (A1 & A2) | B1 | C1 | D1

module sky130_fd_sc_ms__a2111o_sva (
  input logic X,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic C1,
  input logic D1
);
  // Evaluate on any design activity
  default clocking cb @(*); endclocking

  // Functional equivalence when inputs are known
  a_func_eq: assert property (
    !$isunknown({A1,A2,B1,C1,D1}) |-> (X == ((A1 & A2) | B1 | C1 | D1))
  );

  // Output must be known if all inputs are known
  a_known_out: assert property (
    !$isunknown({A1,A2,B1,C1,D1}) |-> !$isunknown(X)
  );

  // Controlling value checks (must assert regardless of other inputs)
  a_ctrl_b1:  assert property (B1  |-> (X == 1'b1));
  a_ctrl_c1:  assert property (C1  |-> (X == 1'b1));
  a_ctrl_d1:  assert property (D1  |-> (X == 1'b1));
  a_ctrl_and: assert property ((A1 & A2) |-> (X == 1'b1));

  // All-zero inputs => output must be 0
  a_zero: assert property ((!A1 && !A2 && !B1 && !C1 && !D1) |-> (X == 1'b0));

  // Only one of A1/A2 high (others low) must not assert output
  a_only_one_a_high: assert property (
    (B1==0 && C1==0 && D1==0 && (A1 ^ A2)) |-> (X == 1'b0)
  );

  // No spurious output changes without an input change
  a_no_spurious: assert property (
    $changed(X) |-> $changed({A1,A2,B1,C1,D1})
  );

  // Key functional coverage
  c_x_low_all_zero: cover property (!A1 && !A2 && !B1 && !C1 && !D1 && !X);

  c_b1_drives: cover property (
    $past(!B1 && !A1 && !A2 && !C1 && !D1) &&
    ( B1 && !A1 && !A2 && !C1 && !D1 && X)
  );

  c_c1_drives: cover property (
    $past(!C1 && !A1 && !A2 && !B1 && !D1) &&
    (!B1 && !A1 && !A2 &&  C1 && !D1 && X)
  );

  c_d1_drives: cover property (
    $past(!D1 && !A1 && !A2 && !B1 && !C1) &&
    (!B1 && !A1 && !A2 && !C1 &&  D1 && X)
  );

  c_and_drives: cover property (
    $past(!(A1 && A2) && !B1 && !C1 && !D1) &&
    (A1 && A2 && !B1 && !C1 && !D1 && X)
  );

  c_x_fall_from_one: cover property (
    $past(X) && !X && !B1 && !C1 && !D1 && !(A1 && A2)
  );

  // Compact truth-table input coverage (all 32 input combinations observed)
  genvar v;
  for (v = 0; v < 32; v++) begin : g_tt_cov
    // Pack order: {A1,A2,B1,C1,D1}
    tt_seen: cover property ( {A1,A2,B1,C1,D1} == 5'(v) );
  end

endmodule

// Bind to DUT
bind sky130_fd_sc_ms__a2111o sky130_fd_sc_ms__a2111o_sva sva_i (.*);