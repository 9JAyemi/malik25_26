// SVA for and_gate
// Bind this module to the DUT to check functionality and collect coverage.

module and_gate_sva (
  input logic a,
  input logic b,
  input logic y,
  input logic and_out
);

  // Sample on any change of inputs or output
  default clocking cb @(posedge a or negedge a or
                        posedge b or negedge b or
                        posedge y or negedge y);
  endclocking

  // Functional equivalence (4-state accurate)
  property p_func; y === (a & b); endproperty
  assert property (p_func) else $error("and_gate: y != (a & b)");

  // Connectivity to internal net
  property p_connect; y === and_out; endproperty
  assert property (p_connect) else $error("and_gate: y != and_out");

  // No X/Z on y when inputs are known
  property p_known;
    !$isunknown({a,b}) |-> ##0 !$isunknown(y);
  endproperty
  assert property (p_known) else $error("and_gate: unknown y with known inputs");

  // Output transitions are logically justified
  assert property (@(posedge y) a && b)
    else $error("and_gate: y rose without a==1 && b==1");
  assert property (@(negedge y) (!a || !b))
    else $error("and_gate: y fell while a==1 && b==1");

  // y should not change without some input changing
  assert property (@(posedge y or negedge y) ($changed(a) || $changed(b)))
    else $error("and_gate: y changed without a/b change");

  // Minimal functional coverage
  cover property ( !a && !b && !y );
  cover property ( !a &&  b && !y );
  cover property (  a && !b && !y );
  cover property (  a &&  b &&  y );

  cover property (@(posedge y) 1'b1);
  cover property (@(negedge y) 1'b1);

endmodule

// Bind into all instances of and_gate
bind and_gate and_gate_sva i_and_gate_sva(.a(a), .b(b), .y(y), .and_out(and_out));