// SVA checker for logic_unit (majority-of-3: x = ab | ac | bc)
module logic_unit_sva (input logic a, b, c, x);

  // Sample on any input/output edge to catch combinational behavior and edges
  default clocking cb @(
      posedge a or negedge a or
      posedge b or negedge b or
      posedge c or negedge c or
      posedge x or negedge x
  ); endclocking

  // Functional correctness when signals are 0/1
  ap_func: assert property (
    !$isunknown({a,b,c,x}) |-> ( x == ((a & b) | (a & c) | (b & c)) )
  );

  // x must be known whenever inputs are known
  ap_no_x: assert property (
    !$isunknown({a,b,c}) |-> !$isunknown(x)
  );

  // x can only change if at least one input changed
  ap_x_dep: assert property (
    @(posedge x or negedge x) $changed({a,b,c})
  );

  // Single-input toggle cause/effect with others stable
  ap_pos_a: assert property (@(posedge a) $stable(b) && $stable(c) |-> ((b ^ c) ? $rose(x) : !$changed(x)));
  ap_pos_b: assert property (@(posedge b) $stable(a) && $stable(c) |-> ((a ^ c) ? $rose(x) : !$changed(x)));
  ap_pos_c: assert property (@(posedge c) $stable(a) && $stable(b) |-> ((a ^ b) ? $rose(x) : !$changed(x)));
  ap_neg_a: assert property (@(negedge a) $stable(b) && $stable(c) |-> ((b ^ c) ? $fell(x) : !$changed(x)));
  ap_neg_b: assert property (@(negedge b) $stable(a) && $stable(c) |-> ((a ^ c) ? $fell(x) : !$changed(x)));
  ap_neg_c: assert property (@(negedge c) $stable(a) && $stable(b) |-> ((a ^ b) ? $fell(x) : !$changed(x)));

  // Truth-table coverage (all 8 input combinations with expected x)
  cv_000: cover property ((!a && !b && !c) && !x);
  cv_001: cover property ((!a && !b &&  c) && !x);
  cv_010: cover property ((!a &&  b && !c) && !x);
  cv_100: cover property (( a && !b && !c) && !x);
  cv_011: cover property ((!a &&  b &&  c) &&  x);
  cv_101: cover property (( a && !b &&  c) &&  x);
  cv_110: cover property (( a &&  b && !c) &&  x);
  cv_111: cover property (( a &&  b &&  c) &&  x);

  // Threshold-crossing edge coverage due to single-input changes
  cv_rise_a: cover property (@(posedge a) $stable(b) && $stable(c) && (b ^ c) && $rose(x));
  cv_rise_b: cover property (@(posedge b) $stable(a) && $stable(c) && (a ^ c) && $rose(x));
  cv_rise_c: cover property (@(posedge c) $stable(a) && $stable(b) && (a ^ b) && $rose(x));
  cv_fall_a: cover property (@(negedge a) $stable(b) && $stable(c) && (b ^ c) && $fell(x));
  cv_fall_b: cover property (@(negedge b) $stable(a) && $stable(c) && (a ^ c) && $fell(x));
  cv_fall_c: cover property (@(negedge c) $stable(a) && $stable(b) && (a ^ b) && $fell(x));

endmodule

// Bind into DUT
bind logic_unit logic_unit_sva u_logic_unit_sva (.*);