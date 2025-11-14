// SVA for mux_system
// Concise, high-value checks and coverage

module mux_system_sva
(
  input logic a, b, c,
  input logic sel_2to1, sel_3to1,
  input logic out
);

  logic exp_l1, exp_out;
  assign exp_l1  = (a & sel_2to1) | (b & ~sel_2to1);
  assign exp_out = ~((exp_l1 & sel_3to1) | (c & ~sel_3to1));

  default clocking cb @(posedge a or negedge a or
                        posedge b or negedge b or
                        posedge c or negedge c or
                        posedge sel_2to1 or negedge sel_2to1 or
                        posedge sel_3to1 or negedge sel_3to1 or
                        posedge out or negedge out); endclocking
  default disable iff ($isunknown({a,b,c,sel_2to1,sel_3to1}));

  // Functional equivalence (allow delta for NBA update)
  a_func: assert property (1 |-> ##0 (out === exp_out))
          else $error("mux_system: functional mismatch");

  // Selection semantics
  a_sel3_1: assert property ( sel_3to1 |-> ##0 (out === ~(sel_2to1 ? a : b)) );
  a_sel3_0: assert property (!sel_3to1 |-> ##0 (out === ~c) );

  // Propagation of the selected data
  a_prop_a: assert property ( sel_3to1 &&  sel_2to1 && $changed(a) |-> ##0 (out === ~a) );
  a_prop_b: assert property ( sel_3to1 && !sel_2to1 && $changed(b) |-> ##0 (out === ~b) );
  a_prop_c: assert property (!sel_3to1 && $changed(c)                  |-> ##0 (out === ~c) );

  // Blocking of unselected data
  a_blk_a: assert property ( (!sel_3to1 || (sel_3to1 && !sel_2to1)) && $changed(a) |-> ##0 !$changed(out) );
  a_blk_b: assert property ( (!sel_3to1 || (sel_3to1 &&  sel_2to1)) && $changed(b) |-> ##0 !$changed(out) );
  a_blk_c: assert property (  sel_3to1 && $changed(c)                                 |-> ##0 !$changed(out) );

  // No X on output when inputs are known
  a_no_x:  assert property ( !$isunknown({a,b,c,sel_2to1,sel_3to1}) |-> ##0 !$isunknown(out) );

  // Coverage: exercise each path and select toggles
  c_path_a:      cover property ( sel_3to1 &&  sel_2to1 ##1 $changed(a) ##0 $changed(out) );
  c_path_b:      cover property ( sel_3to1 && !sel_2to1 ##1 $changed(b) ##0 $changed(out) );
  c_path_c:      cover property (!sel_3to1            ##1 $changed(c) ##0 $changed(out) );
  c_sel2_toggle: cover property ( sel_3to1 ##1 $changed(sel_2to1) ##0 $changed(out) );
  c_sel3_toggle: cover property ( $changed(sel_3to1) ##0 $changed(out) );

endmodule

bind mux_system mux_system_sva sva_mux_system (.*);