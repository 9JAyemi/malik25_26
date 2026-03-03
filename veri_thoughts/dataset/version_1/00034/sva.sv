// SVA for karnaugh_map
module karnaugh_map_sva(input logic A, B, C, D, F);

  // Sample on any input change
  default clocking cb @(A or B or C or D); endclocking

  // Functional equivalence (primary check)
  ap_func: assert property (disable iff ($isunknown({A,B,C}))
                            F === (!A && (B || C)));

  // Output must be 0 whenever A=1 (redundant safety check)
  ap_a_dominates: assert property (A |-> !F);

  // No X/Z on F when inputs are known
  ap_no_x: assert property ((!$isunknown({A,B,C})) |-> !$isunknown(F));

  // Independence from D: changing D with A,B,C stable must not change F
  ap_d_indep: assert property (($stable({A,B,C}) && $changed(D)) |-> $stable(F));

  // Truth-table coverage for all A,B, C combinations (full functional coverage)
  cp_000: cover property ({A,B,C}==3'b000 && !F);
  cp_001: cover property ({A,B,C}==3'b001 &&  F);
  cp_010: cover property ({A,B,C}==3'b010 &&  F);
  cp_011: cover property ({A,B,C}==3'b011 &&  F);
  cp_100: cover property ({A,B,C}==3'b100 && !F);
  cp_101: cover property ({A,B,C}==3'b101 && !F);
  cp_110: cover property ({A,B,C}==3'b110 && !F);
  cp_111: cover property ({A,B,C}==3'b111 && !F);

  // Cover that D toggles while A,B,C are stable and F remains unchanged
  cp_d_toggle: cover property ($stable({A,B,C}) && $changed(D) && $stable(F));

endmodule

// Bind into DUT
bind karnaugh_map karnaugh_map_sva sva_i(.A(A), .B(B), .C(C), .D(D), .F(F));