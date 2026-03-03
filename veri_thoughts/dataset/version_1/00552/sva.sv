// SVA for karnaugh_map: concise, functionally complete, and with full input coverage
module karnaugh_map_sva (input logic A, B, C, F);

  // Sample on any relevant combinational activity
  default clocking cb @(A or B or C or F); endclocking

  // Functional equivalence: F must equal A whenever inputs are known
  a_func:        assert property (disable iff ($isunknown({A,B,C}))) (F == A);

  // F follows A immediately on A changes
  a_a_follow:    assert property (@(A) disable iff ($isunknown({A,B,C}))) ##0 (F == A);

  // B/C changes must not affect F when A is stable
  a_bc_noeffect: assert property (@(B or C) disable iff ($isunknown({A,B,C})))
                               (!$changed(A)) |-> ##0 (!$changed(F) && (F == $past(F)));

  // No spurious output changes: any F change must be caused by an input change
  a_no_spurious: assert property (@(F) disable iff ($isunknown({A,B,C})))
                               $changed(F) |-> ($changed(A) || $changed(B) || $changed(C));

  // Input-space coverage (all 8 minterms reached)
  c_000: cover property ({A,B,C} == 3'b000);
  c_001: cover property ({A,B,C} == 3'b001);
  c_010: cover property ({A,B,C} == 3'b010);
  c_011: cover property ({A,B,C} == 3'b011);
  c_100: cover property ({A,B,C} == 3'b100);
  c_101: cover property ({A,B,C} == 3'b101);
  c_110: cover property ({A,B,C} == 3'b110);
  c_111: cover property ({A,B,C} == 3'b111);

  // Output transition coverage tied to A transitions
  c_a_rise: cover property (@(A) $rose(A) ##0 (F == 1'b1));
  c_a_fall: cover property (@(A) $fell(A) ##0 (F == 1'b0));

endmodule

// Bind into the DUT
bind karnaugh_map karnaugh_map_sva kmap_chk (.A(A), .B(B), .C(C), .F(F));