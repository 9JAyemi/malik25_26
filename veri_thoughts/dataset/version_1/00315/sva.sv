// SVA for sky130_fd_sc_ls__a21o
// Bind into DUT; checks functional equivalence, structure, known-ness, and full input-space coverage.

module sky130_fd_sc_ls__a21o_sva (
  input logic A1, A2, B1, X,
  input logic and0_out, or0_out_X
);

  // Functional equivalence (combinational)
  a_func:    assert property ( X === ((A1 & A2) | B1) );

  // Structural/local checks
  a_and:     assert property ( and0_out  === (A1 & A2) );
  a_or:      assert property ( or0_out_X === (and0_out | B1) );
  a_buf:     assert property ( X === or0_out_X );

  // Dominance and partitioned correctness
  a_dom_b1:  assert property ( B1 |-> X );
  a_b1low:   assert property ( !B1 |-> (X === (A1 & A2)) );
  a_dom_and: assert property ( (A1 & A2) |-> X );

  // Known-ness: if inputs are known, all internal/outputs must be known
  a_known:   assert property ( !$isunknown({A1,A2,B1}) |-> (!$isunknown(and0_out) && !$isunknown(or0_out_X) && !$isunknown(X)) );

  // Input-space coverage (all 8 cubes with expected X)
  c_000: cover property ( !A1 && !A2 && !B1 && !X );
  c_001: cover property ( !A1 && !A2 &&  B1 &&  X );
  c_010: cover property ( !A1 &&  A2 && !B1 && !X );
  c_011: cover property ( !A1 &&  A2 &&  B1 &&  X );
  c_100: cover property (  A1 && !A2 && !B1 && !X );
  c_101: cover property (  A1 && !A2 &&  B1 &&  X );
  c_110: cover property (  A1 &&  A2 && !B1 &&  X );
  c_111: cover property (  A1 &&  A2 &&  B1 &&  X );

  // Output toggle coverage
  cx_rise: cover property ( $rose(X) );
  cx_fall: cover property ( $fell(X) );

endmodule

bind sky130_fd_sc_ls__a21o sky130_fd_sc_ls__a21o_sva sva (.*);