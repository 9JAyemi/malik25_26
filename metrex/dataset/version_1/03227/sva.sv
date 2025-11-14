// SVA for and_gate: concise, high-quality checks and coverage
module and_gate_sva (
  input logic Y,
  input logic A1, A2, A3, A4, B1
);

  // Sample on any relevant edge to catch combinational updates
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge A4 or negedge A4 or
    posedge B1 or negedge B1 or
    posedge Y  or negedge Y
  ); endclocking

  // Functional equivalence when inputs are known (avoid false fails on Xs)
  assert property ( !$isunknown({A1,A2,A3,A4,B1}) |-> ##0 (Y == (A1 & A2 & A3 & A4 & B1)) )
    else $error("AND mismatch");

  // Output should never be X/Z
  assert property ( !$isunknown(Y) )
    else $error("Y is X/Z");

  // No spurious Y change without an input change
  assert property ( $changed(Y) |-> $changed({A1,A2,A3,A4,B1}) )
    else $error("Y changed without input change");

  // Extremes (clarity)
  assert property ( (!$isunknown({A1,A2,A3,A4,B1}) && &{A1,A2,A3,A4,B1}) |-> ##0 (Y == 1) );
  assert property ( (!$isunknown({A1,A2,A3,A4,B1}) && (!A1 || !A2 || !A3 || !A4 || !B1)) |-> ##0 (Y == 0) );

  // Coverage: observe key scenarios and individual input control of Y
  cover property ( &{A1,A2,A3,A4,B1} ##0 (Y == 1) ); // all ones drives Y high

  cover property ( &{A2,A3,A4,B1} && $rose(A1) |-> ##0 $rose(Y) );
  cover property ( &{A2,A3,A4,B1} && $fell(A1) |-> ##0 $fell(Y) );

  cover property ( &{A1,A3,A4,B1} && $rose(A2) |-> ##0 $rose(Y) );
  cover property ( &{A1,A3,A4,B1} && $fell(A2) |-> ##0 $fell(Y) );

  cover property ( &{A1,A2,A4,B1} && $rose(A3) |-> ##0 $rose(Y) );
  cover property ( &{A1,A2,A4,B1} && $fell(A3) |-> ##0 $fell(Y) );

  cover property ( &{A1,A2,A3,B1} && $rose(A4) |-> ##0 $rose(Y) );
  cover property ( &{A1,A2,A3,B1} && $fell(A4) |-> ##0 $fell(Y) );

  cover property ( &{A1,A2,A3,A4} && $rose(B1) |-> ##0 $rose(Y) );
  cover property ( &{A1,A2,A3,A4} && $fell(B1) |-> ##0 $fell(Y) );

endmodule

// Bind into the DUT
bind and_gate and_gate_sva u_and_gate_sva (.*);