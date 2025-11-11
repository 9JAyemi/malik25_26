// SVA for karnaugh_map_5: F must equal (~A & E) and be independent of B,C,D.
// Bind into DUT for automatic checking.

module karnaugh_map_5_sva (
  input logic A, B, C, D, E,
  input logic F
);
  let f_exp = (~A) & E;

  // Functional equivalence (combinational, with X/Z guard on inputs)
  property p_func_equiv;
    @(A or B or C or D or E) (!$isunknown({A,B,C,D,E})) |-> ##0 (F == f_exp);
  endproperty
  assert property (p_func_equiv);

  // Independence: B/C/D changes must not affect F when A and E are stable
  property p_indep_bcd;
    @(B or C or D)
      (($changed(B) || $changed(C) || $changed(D)) && $stable(A) && $stable(E) && !$isunknown({A,E}))
      |-> ##0 $stable(F);
  endproperty
  assert property (p_indep_bcd);

  // Response to A changes when E==1
  property p_resp_A;
    @(A) $changed(A) && $stable(E) && (E==1'b1) |-> ##0 (F == ~A);
  endproperty
  assert property (p_resp_A);

  // Response to E changes
  property p_resp_E;
    @(E) $changed(E) && $stable(A) |-> ##0 (F == f_exp);
  endproperty
  assert property (p_resp_E);

  // Minimal, meaningful coverage
  cover property (@(A or B or C or D or E) (!A && E));   // F==1 region
  cover property (@(A or B or C or D or E) (A && E));    // F==0 region
  cover property (@(A or B or C or D or E) (!A && !E));  // F==0 region
  cover property (@(A or B or C or D or E) (A && !E));   // F==0 region
  cover property (@(A or B or C or D or E or F) $rose(F));
  cover property (@(A or B or C or D or E or F) $fell(F));
endmodule

bind karnaugh_map_5 karnaugh_map_5_sva u_karnaugh_map_5_sva (
  .A(A), .B(B), .C(C), .D(D), .E(E), .F(F)
);