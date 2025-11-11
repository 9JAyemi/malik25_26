// SVA for four_input_or
module four_input_or_sva (
  input logic A, B, C, D,
  input logic X
);

  // Functional correctness when inputs are known
  assert property ( !$isunknown({A,B,C,D}) |-> (X == (A|B|C|D)) && !$isunknown(X) );

  // Output can be X only if at least one input is X/Z
  assert property ( $isunknown(X) |-> $isunknown({A,B,C,D}) );

  // Strong OR extremes (hold regardless of unknowns on other inputs)
  assert property ( ((A|B|C|D) === 1'b1) |-> (X === 1'b1) );
  assert property ( ((A|B|C|D) === 1'b0) |-> (X === 1'b0) );

  // Zero-delay combinational behavior on any input change with known inputs
  assert property ( !$isunknown({A,B,C,D}) && $changed({A,B,C,D}) |-> ##0 (X == (A|B|C|D)) );

  // Coverage: key truth-table points and X toggling
  cover property ( !A && !B && !C && !D && (X === 1'b0) );
  cover property (  A && !B && !C && !D && (X === 1'b1) );
  cover property ( !A &&  B && !C && !D && (X === 1'b1) );
  cover property ( !A && !B &&  C && !D && (X === 1'b1) );
  cover property ( !A && !B && !C &&  D && (X === 1'b1) );
  cover property ( $countones({A,B,C,D}) >= 2 && (X === 1'b1) );
  cover property ( $rose(X) );
  cover property ( $fell(X) );

endmodule

bind four_input_or four_input_or_sva sva_inst (.*);