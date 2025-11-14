// SVA for XORCY: O must be CI ^ LI, no spurious toggles, concise full coverage
module XORCY_sva(input logic CI, LI, O);

  // Sample on any edge of inputs or output
  default clocking cb @(posedge CI or negedge CI or posedge LI or negedge LI or posedge O or negedge O); endclocking

  // Functional correctness (when inputs are known, output matches XOR after delta)
  a_xor_correct: assert property( !$isunknown({CI,LI}) |-> ##0 (O === (CI ^ LI)) );

  // Output changes only if exactly one input changed
  a_o_change_cause: assert property( $changed(O) |-> ($changed(CI) ^ $changed(LI)) );

  // Exactly one input change forces output change and correct value
  a_single_input_effect: assert property( (!$isunknown({CI,LI})) && ($changed(CI) ^ $changed(LI))
                                          |-> ##0 ($changed(O) && O === (CI ^ LI)) );

  // Coverage: all stable states observed (inputs/outputs known)
  c_state_00: cover property( !$isunknown({CI,LI,O}) && {CI,LI,O} == 3'b000 );
  c_state_01: cover property( !$isunknown({CI,LI,O}) && {CI,LI,O} == 3'b011 );
  c_state_10: cover property( !$isunknown({CI,LI,O}) && {CI,LI,O} == 3'b101 );
  c_state_11: cover property( !$isunknown({CI,LI,O}) && {CI,LI,O} == 3'b110 );

  // Coverage: single-input toggles cause O toggle
  c_ci_toggle: cover property( !$isunknown({CI,LI}) && $changed(CI) && !$changed(LI) ##0 $changed(O) );
  c_li_toggle: cover property( !$isunknown({CI,LI}) && $changed(LI) && !$changed(CI) ##0 $changed(O) );

  // Coverage: simultaneous toggles keep O stable
  c_both_toggle_no_o: cover property( $changed(CI) && $changed(LI) ##0 !$changed(O) );

endmodule

// Bind into DUT
bind XORCY XORCY_sva xorcy_sva_i(.CI(CI), .LI(LI), .O(O));