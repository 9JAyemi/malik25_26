// SVA checker for mux_4to1
module mux_4to1_sva (
    input logic a, b, c, d,
    input logic sel_1, sel_0,
    input logic out_always
);
  // Sample on any relevant signal edge
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge c or negedge c or
    posedge d or negedge d or
    posedge sel_1 or negedge sel_1 or
    posedge sel_0 or negedge sel_0
  ); endclocking

  // 4-state decode to mirror the DUT's if/else chain
  logic cond0, cond1, cond2;
  assign cond0 = (sel_1 === 1'b0) && (sel_0 === 1'b0);
  assign cond1 = (sel_1 === 1'b0) && (sel_0 === 1'b1);
  assign cond2 = (sel_1 === 1'b1) && (sel_0 === 1'b0);

  // Functional correctness (exactly mirrors DUT semantics)
  a_path: assert property ( cond0 |-> (out_always === a) );
  b_path: assert property ( (!cond0 && cond1) |-> (out_always === b) );
  c_path: assert property ( (!cond0 && !cond1 && cond2) |-> (out_always === c) );
  d_path: assert property ( (!cond0 && !cond1 && !cond2) |-> (out_always === d) );

  // No-X on output when selected input and selects are known
  nox_a: assert property ( cond0 && !$isunknown(a) |-> !$isunknown(out_always) );
  nox_b: assert property ( (!cond0 && cond1) && !$isunknown(b) |-> !$isunknown(out_always) );
  nox_c: assert property ( (!cond0 && !cond1 && cond2) && !$isunknown(c) |-> !$isunknown(out_always) );
  nox_d: assert property ( (!cond0 && !cond1 && !cond2) && !$isunknown(d) |-> !$isunknown(out_always) );

  // Functional coverage of all select combos
  cover_sel_00: cover property ( cond0 );
  cover_sel_01: cover property ( cond1 );
  cover_sel_10: cover property ( cond2 );
  cover_sel_11: cover property ( (sel_1 === 1'b1) && (sel_0 === 1'b1) );

  // Propagation coverage: selected input toggle is reflected on output immediately
  cover_a_path_toggle: cover property ( cond0 ##1 $changed(a) ##0 (out_always === a) );
  cover_b_path_toggle: cover property ( (!cond0 && cond1) ##1 $changed(b) ##0 (out_always === b) );
  cover_c_path_toggle: cover property ( (!cond0 && !cond1 && cond2) ##1 $changed(c) ##0 (out_always === c) );
  cover_d_path_toggle: cover property ( (!cond0 && !cond1 && !cond2) ##1 $changed(d) ##0 (out_always === d) );
endmodule

// Bind into DUT
bind mux_4to1 mux_4to1_sva i_mux_4to1_sva (.*);