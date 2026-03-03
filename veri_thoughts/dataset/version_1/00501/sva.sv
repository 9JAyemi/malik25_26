// SVA for nor3_module
// Bind this file alongside the DUT

`default_nettype none

module nor3_module_sva;
  // This bind module lives in nor3_module scope; it can see A,B,C_N,Y, VPWR, VGND

  // Power rails are correct
  a_power_rails_const: assert property (@(*)
    (VPWR === 1'b1) && (VGND === 1'b0));

  // Functional equivalence (4-state clean when inputs known)
  a_func_equiv_known: assert property (@(*)
    (!$isunknown({A,B,C_N})) |-> (Y === ~(A | B | C_N)));

  // One-way implications (X-safe)
  a_any_high_forces_low:  assert property (@(*)
    (A===1'b1 || B===1'b1 || C_N===1'b1) |-> (Y===1'b0));

  a_all_low_forces_high:  assert property (@(*)
    (A===1'b0 && B===1'b0 && C_N===1'b0) |-> (Y===1'b1));

  // Output is known if inputs are known
  a_known_out_if_known_in: assert property (@(*)
    (!$isunknown({A,B,C_N})) |-> !$isunknown(Y));

  // Purely combinational: no Y change without input change
  a_no_spurious_y_change: assert property (@(*)
    ($stable(A) && $stable(B) && $stable(C_N)) |-> $stable(Y));

  // Zero-delay response on edges
  a_rise_any_input_makes_y0: assert property (@(*)
    ($rose(A) || $rose(B) || $rose(C_N)) |-> (Y===1'b0));

  a_fall_A_to_all_zero_makes_y1: assert property (@(*)
    ($fell(A) && (B===1'b0) && (C_N===1'b0)) |-> (Y===1'b1));
  a_fall_B_to_all_zero_makes_y1: assert property (@(*)
    ($fell(B) && (A===1'b0) && (C_N===1'b0)) |-> (Y===1'b1));
  a_fall_C_to_all_zero_makes_y1: assert property (@(*)
    ($fell(C_N) && (A===1'b0) && (B===1'b0)) |-> (Y===1'b1));

  // Truth-table coverage (all 8 input combinations with expected Y)
  c_tt_000: cover property (@(*) (A===1'b0 && B===1'b0 && C_N===1'b0 && Y===1'b1));
  c_tt_001: cover property (@(*) (A===1'b0 && B===1'b0 && C_N===1'b1 && Y===1'b0));
  c_tt_010: cover property (@(*) (A===1'b0 && B===1'b1 && C_N===1'b0 && Y===1'b0));
  c_tt_011: cover property (@(*) (A===1'b0 && B===1'b1 && C_N===1'b1 && Y===1'b0));
  c_tt_100: cover property (@(*) (A===1'b1 && B===1'b0 && C_N===1'b0 && Y===1'b0));
  c_tt_101: cover property (@(*) (A===1'b1 && B===1'b0 && C_N===1'b1 && Y===1'b0));
  c_tt_110: cover property (@(*) (A===1'b1 && B===1'b1 && C_N===1'b0 && Y===1'b0));
  c_tt_111: cover property (@(*) (A===1'b1 && B===1'b1 && C_N===1'b1 && Y===1'b0));

  // Output toggle coverage
  c_y_rise: cover property (@(*) $rose(Y));
  c_y_fall: cover property (@(*) $fell(Y));
endmodule

bind nor3_module nor3_module_sva i_nor3_module_sva();