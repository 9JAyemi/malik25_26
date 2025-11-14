// SVA checker for six_signal_module
// Focus: functional equivalence, X-prop, stability, unateness, concise yet comprehensive coverage

module six_signal_module_sva (
  input logic A1, A2, B1, B2, C1,
  input logic Y
);
  default clocking cb @(posedge $global_clock); endclocking

  function automatic logic y_ref(logic A1, A2, B1, B2, C1);
    y_ref = (A1 & A2) | (B1 & B2) | (C1 & (A1 | A2));
  endfunction

  // Golden equivalence (4-state) and clean-input equivalence (2-state)
  ap_equiv_4state: assert property (Y === y_ref(A1,A2,B1,B2,C1));
  ap_equiv_clean:  assert property (!$isunknown({A1,A2,B1,B2,C1}))
                                |-> (! $isunknown(Y) && (Y == y_ref(A1,A2,B1,B2,C1)));

  // Purely combinational: if inputs are stable, Y must be stable
  ap_stable: assert property ($stable({A1,A2,B1,B2,C1}) |-> $stable(Y));

  // Each product term implies Y=1 (helpful localization)
  ap_imp_A: assert property ((A1 && A2) |-> Y);
  ap_imp_B: assert property ((B1 && B2) |-> Y);
  ap_imp_C: assert property ((C1 && (A1 || A2)) |-> Y);

  // Simplified reductions in common modes
  ap_c1_0:  assert property ((!C1) |-> (Y == ((A1 && A2) || (B1 && B2))));
  ap_a_zero: assert property ((!A1 && !A2) |-> (Y == (B1 && B2)));

  // Positive unateness under single-input rise with others stable
  ap_unate_A1: assert property ($rose(A1) && $stable({A2,B1,B2,C1}) |-> !$fell(Y));
  ap_unate_A2: assert property ($rose(A2) && $stable({A1,B1,B2,C1}) |-> !$fell(Y));
  ap_unate_B1: assert property ($rose(B1) && $stable({A1,A2,B2,C1}) |-> !$fell(Y));
  ap_unate_B2: assert property ($rose(B2) && $stable({A1,A2,B1,C1}) |-> !$fell(Y));
  ap_unate_C1: assert property ($rose(C1) && $stable({A1,A2,B1,B2}) |-> !$fell(Y));

  // Coverage: all 32 input combinations
  logic [4:0] in;
  assign in = {A1,A2,B1,B2,C1};
  genvar i;
  generate
    for (i=0; i<32; i++) begin : g_all_inputs
      cp_in_all: cover property (in == i[4:0]);
    end
  endgenerate

  // Coverage: basic output behavior and dominance/overlap scenarios
  cp_y0: cover property (!Y);
  cp_y1: cover property (Y);
  cp_A_only: cover property (!C1 && A1 && A2 && !(B1 && B2) && Y);
  cp_B_only: cover property (B1 && B2 && !A1 && !A2 && Y);
  cp_C_only: cover property (C1 && (A1 ^ A2) && !(B1 && B2) && Y);
  cp_AB_overlap:   cover property (A1 && A2 && B1 && B2 && Y);
  cp_AC_overlap:   cover property (A1 && A2 && C1 && Y);
  cp_BC_overlap:   cover property (B1 && B2 && C1 && (A1 || A2) && Y);
  cp_all_overlap:  cover property (A1 && A2 && B1 && B2 && C1 && Y);
  cp_rose: cover property ($rose(Y));
  cp_fell: cover property ($fell(Y));
endmodule

// Bind into the DUT
bind six_signal_module six_signal_module_sva
  (.A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .Y(Y));