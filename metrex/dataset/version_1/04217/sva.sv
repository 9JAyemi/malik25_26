// SVA for mux2to1
module mux2to1_sva (input logic o, a, b, sel);

  // Sample on any edge of inputs or output; use ##0 to avoid preponed sampling races
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge sel or negedge sel or
    posedge o or negedge o
  ); endclocking

  // Functional equivalence (4-state accurate)
  assert property ( $changed({a,b,sel}) |-> ##0 (o === (sel ? b : a)) )
    else $error("mux2to1: functional mismatch");

  // Select control behavior
  assert property ( $rose(sel) |-> ##0 (o === b) );
  assert property ( $fell(sel) |-> ##0 (o === a) );

  // Unsselected input must not affect output; selected input must drive output
  assert property ( (sel==0) && $changed(a) && $stable({b,sel}) |-> ##0 (o===a) );
  assert property ( (sel==1) && $changed(b) && $stable({a,sel}) |-> ##0 (o===b) );
  assert property ( (sel==0) && $changed(b) && $stable({a,sel}) |-> ##0 $stable(o) );
  assert property ( (sel==1) && $changed(a) && $stable({b,sel}) |-> ##0 $stable(o) );

  // 2-state inputs produce 2-state output
  assert property ( (!$isunknown({a,b,sel})) |-> ##0 (!$isunknown(o)) );

  // X/Z select propagation semantics
  assert property ( $isunknown(sel) && (a===b) |-> ##0 (o===a) );
  assert property ( $isunknown(sel) && (a!==b) |-> ##0 $isunknown(o) );

  // Coverage
  cover property ( $rose(sel) ##0 (o===b) );
  cover property ( $fell(sel) ##0 (o===a) );
  cover property ( (sel==0) && $changed(a) ##0 (o===a) );
  cover property ( (sel==1) && $changed(b) ##0 (o===b) );
  cover property ( $isunknown(sel) && (a===b) ##0 (o===a) );
  cover property ( $isunknown(sel) && (a!==b) ##0 $isunknown(o) );

endmodule

// Bind into DUT
bind mux2to1 mux2to1_sva mux2to1_sva_i(.o(o), .a(a), .b(b), .sel(sel));