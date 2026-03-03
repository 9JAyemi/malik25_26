// SVA for XNOR3HD2X
module XNOR3HD2X_sva(input logic A, B, C, Z);

  // Sample on any input/output edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge Z or negedge Z
  ); endclocking

  // Functional correctness for known inputs
  ap_func: assert property ( !$isunknown({A,B,C}) |-> (Z === ~(^ {A,B,C})) );

  // X-propagation: any unknown on inputs must produce unknown Z
  ap_xprop: assert property ( $isunknown({A,B,C}) |-> $isunknown(Z) );

  // No spurious toggles: Z can only change when some input changes
  ap_no_spurious: assert property ( $changed(Z) |-> $changed({A,B,C}) );

  // Parity-change behavior
  ap_toggle_1: assert property (
    !$isunknown({A,B,C}) &&
    ( ($changed(A) && !$changed(B) && !$changed(C)) ||
      (!$changed(A) && $changed(B) && !$changed(C)) ||
      (!$changed(A) && !$changed(B) && $changed(C)) )
    |-> $changed(Z)
  );

  ap_toggle_2: assert property (
    !$isunknown({A,B,C}) &&
    ( ($changed(A) && $changed(B) && !$changed(C)) ||
      ($changed(A) && !$changed(B) && $changed(C)) ||
      (!$changed(A) && $changed(B) && $changed(C)) )
    |-> !$changed(Z)
  );

  ap_toggle_3: assert property (
    !$isunknown({A,B,C}) &&
    ($changed(A) && $changed(B) && $changed(C)) |-> $changed(Z)
  );

  // Full truth-table coverage (known states)
  cp_000: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b0001);
  cp_001: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b0010);
  cp_010: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b0100);
  cp_011: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b0111);
  cp_100: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b1000);
  cp_101: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b1011);
  cp_110: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b1101);
  cp_111: cover property (!$isunknown({A,B,C,Z}) && {A,B,C,Z} == 4'b1110);

  // X-propagation coverage
  cp_xprop: cover property ($isunknown({A,B,C}) && $isunknown(Z));

endmodule

// Bind into DUT
bind XNOR3HD2X XNOR3HD2X_sva sva(.A(A), .B(B), .C(C), .Z(Z));