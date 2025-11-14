// SVA for clock_module
module clock_module_sva (
  input wire inclk0,
  input wire c0,
  input wire c1,
  input wire locked,
  input wire e0
);

  // Functional equivalence and complement (sampled on both edges of inclk0)
  a_c0_passthru: assert property (@(posedge inclk0 or negedge inclk0) c0 === inclk0);
  a_c1_passthru: assert property (@(posedge inclk0 or negedge inclk0) c1 === inclk0);
  a_e0_inv:      assert property (@(posedge inclk0 or negedge inclk0) e0 === ~inclk0);
  a_locked_one:  assert property (@(posedge inclk0 or negedge inclk0) locked === 1'b1);

  a_c0_c1_equal: assert property (@(posedge inclk0 or negedge inclk0) c0 === c1);
  a_e0_compl:    assert property (@(posedge inclk0 or negedge inclk0) (c0 === ~e0) && (c1 === ~e0));

  // Edge alignment
  a_posedge_align: assert property (@(posedge inclk0)  $rose(c0) && $rose(c1) && $fell(e0));
  a_negedge_align: assert property (@(negedge inclk0)  $fell(c0) && $fell(c1) && $rose(e0));

  // No glitches: outputs only change when input changes, and vice versa
  a_c0_only_with_in: assert property (@(posedge c0 or negedge c0) $changed(inclk0));
  a_c1_only_with_in: assert property (@(posedge c1 or negedge c1) $changed(inclk0));
  a_e0_only_with_in: assert property (@(posedge e0 or negedge e0) $changed(inclk0));
  a_in_drives_outs:  assert property (@(posedge inclk0 or negedge inclk0) $changed(c0) && $changed(c1) && $changed(e0));

  // 4-state propagation / no X
  a_xmap_c0:     assert property (@(posedge inclk0 or negedge inclk0) ($isunknown(c0) == $isunknown(inclk0)));
  a_xmap_c1:     assert property (@(posedge inclk0 or negedge inclk0) ($isunknown(c1) == $isunknown(inclk0)));
  a_xmap_e0:     assert property (@(posedge inclk0 or negedge inclk0) ($isunknown(e0) == $isunknown(inclk0)));
  a_locked_nx:   assert property (@(posedge inclk0 or negedge inclk0) !$isunknown(locked));

  // locked must never change
  a_locked_const: assert property (@(posedge locked or negedge locked) 1'b0);

  // Coverage
  c_posedge: cover property (@(posedge inclk0)  $rose(c0) && $rose(c1) && $fell(e0));
  c_negedge: cover property (@(negedge inclk0)  $fell(c0) && $fell(c1) && $rose(e0));
  c_known_clk: cover property (@(posedge inclk0 or negedge inclk0) !$isunknown(inclk0));

endmodule

// Bind into DUT
bind clock_module clock_module_sva u_clock_module_sva (.*);