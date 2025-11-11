// SVA for dff_en: D-FF with enable; checks functional correctness, gating, and glitch-free Q
module dff_en_sva (input logic D, C, E, Q);

  // Use clocked sampling at posedge C; use ##0 to observe Q after NBA updates
  default clocking cb @(posedge C); endclocking

  // Sanity: inputs not X at sampling edge
  a_no_x_inputs: assert property (!$isunknown({E,D}));

  // Functional correctness
  a_load: assert property (E  |-> ##0 (Q == $sampled(D)));
  a_hold: assert property (!E |-> ##0 (Q == $sampled(Q)));

  // Gating: Q can change only when enabled, and must change when enabled with different data
  a_change_only_if_en: assert property (1 |-> ##0 ($changed(Q) -> $sampled(E)));
  a_must_change_when_diff: assert property ((E && ($sampled(D) != $sampled(Q))) |-> ##0 $changed(Q));

  // No glitches between clock edges
  a_no_glitch: assert property (!$rose(C) |-> $stable(Q));

  // Coverage
  c_load_change: cover property (E && ($sampled(D) != $sampled(Q)) |-> ##0 $changed(Q));
  c_load_same:   cover property (E && ($sampled(D) == $sampled(Q)) |-> ##0 !$changed(Q));
  c_hold:        cover property (!E |-> ##0 !$changed(Q));

endmodule

// Bind to all instances of dff_en
bind dff_en dff_en_sva dff_en_sva_i(.D(D), .C(C), .E(E), .Q(Q));