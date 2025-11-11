// SVA for and_gate
// Concise, high-quality checks for functionality, reset behavior, X-propagation, and basic coverage.

module and_gate_sva (input a, input b, input rst, input out);

  // Sample on any input edge; use ##0 in consequents to check post-NBA value of out
  default clocking cb @(posedge a or negedge a or posedge b or negedge b or posedge rst or negedge rst); endclocking

  // Functional correctness (including reset behavior)
  // When inputs are known, out must equal rst ? (a & b) : 1'b0
  property p_func;
    !$isunknown({rst,a,b}) |-> ##0 (out == (rst ? (a & b) : 1'b0));
  endproperty
  assert property (p_func);

  // Strong implications of AND when enabled by rst
  assert property ( (!$isunknown({rst,a,b})) && rst && out |-> ##0 (a && b) );
  assert property ( (!$isunknown({rst,a,b})) && rst && a && b |-> ##0 out );

  // Out should never be X/Z when driving conditions are known
  assert property ( (!$isunknown({rst,a,b})) |-> ##0 (!$isunknown(out)) );

  // Basic coverages: all input combos under rst plus reset-low case
  cover property ( rst && (a==0) && (b==0) ##0 (out==0) );
  cover property ( rst && (a==0) && (b==1) ##0 (out==0) );
  cover property ( rst && (a==1) && (b==0) ##0 (out==0) );
  cover property ( rst && (a==1) && (b==1) ##0 (out==1) );
  cover property ( !rst ##0 (out==0) );

  // Reset transitions are exercised
  cover property ( !rst ##1 rst );
  cover property ( rst ##1 !rst );

endmodule

// Bind into DUT
bind and_gate and_gate_sva u_and_gate_sva (.*);