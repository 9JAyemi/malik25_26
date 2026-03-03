// SVA for sky130_fd_sc_ls__o21a: X = (A1 | A2) & B1
// Clockless concurrent properties (continuous checking)

module sky130_fd_sc_ls__o21a_sva;

  // Functional equivalence (4-state)
  ap_func:    assert property ( X === ((A1 | A2) & B1) );

  // Internal structure consistency
  ap_or:      assert property ( or0_out    === (A1 | A2) );
  ap_and:     assert property ( and0_out_X === (or0_out & B1) );
  ap_buf:     assert property ( X          === and0_out_X );

  // Deterministic cases and X-propagation sanity
  ap_b0_0:    assert property ( B1 === 1'b0 |-> X === 1'b0 );
  ap_b1_or:   assert property ( B1 === 1'b1 |-> X === (A1 | A2) );
  ap_no_x_ok: assert property ( !$isunknown({A1,A2,B1}) |-> !$isunknown(X) );

  // Coverage: exercise key truth-table regions and each OR leg
  cp_b0:        cover property ( B1 == 1'b0 );
  cp_or0:       cover property ( B1 && (A1==1'b0) && (A2==1'b0) );
  cp_a1_only:   cover property ( B1 && (A1==1'b1) && (A2==1'b0) );
  cp_a2_only:   cover property ( B1 && (A1==1'b0) && (A2==1'b1) );
  cp_both1:     cover property ( B1 && (A1==1'b1) && (A2==1'b1) );
  cp_toggles:   cover property ( $changed({A1,A2,B1}) );

endmodule

// Bind into DUT instances
bind sky130_fd_sc_ls__o21a sky130_fd_sc_ls__o21a_sva sva_i();