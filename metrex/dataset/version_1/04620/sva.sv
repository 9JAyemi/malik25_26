// SVA for sky130_fd_sc_lp__o21a: X = (A1 | A2) & B1
// Bind into the DUT to access internal nets
bind sky130_fd_sc_lp__o21a sky130_fd_sc_lp__o21a_sva u_sva();

module sky130_fd_sc_lp__o21a_sva;

  // Functional truth-table check when inputs are known (no X/Z)
  // Ensures deterministic 0/1 output and correct logic
  assert property (@(*)
    !$isunknown({A1,A2,B1}) |-> (X == ((A1 || A2) && B1))
  ) else $error("o21a: Functional mismatch with known inputs");

  // 4-state structural checks against internal nets
  assert property (@(*)
    or0_out === (A1 | A2)
  ) else $error("o21a: or0_out != (A1 | A2)");

  assert property (@(*)
    and0_out_X === (or0_out & B1)
  ) else $error("o21a: and0_out_X != (or0_out & B1)");

  assert property (@(*)
    X === and0_out_X
  ) else $error("o21a: X != and0_out_X");

  // No X/Z on internal nets and output when inputs are known
  assert property (@(*)
    !$isunknown({A1,A2,B1}) |-> (! $isunknown(or0_out) && ! $isunknown(and0_out_X) && ! $isunknown(X))
  ) else $error("o21a: Unknown on internal/output with known inputs");

  // Coverage: hit all 8 input combinations (with known inputs)
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b000);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b001);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b010);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b011);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b100);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b101);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b110);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b111);

  // Coverage: both output values observed with known inputs
  cover property (@(*) ! $isunknown({A1,A2,B1}) && X == 1'b0);
  cover property (@(*) ! $isunknown({A1,A2,B1}) && X == 1'b1);

endmodule