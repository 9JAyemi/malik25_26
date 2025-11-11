// SVA for mux_2_1
module mux_2_1_sva (input logic A, B, S, Y);

  // Sample on any change of inputs/outputs (combinational)
  clocking cb @ (A or B or S or Y); endclocking
  default clocking cb;

  // Functional equivalence (including 4-state semantics)
  ap_func: assert property (Y === (S ? B : A));

  // Y follows selected input immediately on its change
  ap_follow_A: assert property ((S === 1'b0 && $changed(A)) |-> ##0 ($changed(Y) && Y === A));
  ap_follow_B: assert property ((S === 1'b1 && $changed(B)) |-> ##0 ($changed(Y) && Y === B));

  // Unselected input must not affect Y when select is stable
  ap_ignore_B: assert property ((S === 1'b0 && $changed(B) && !$changed(S) && !$changed(A)) |-> ##0 !$changed(Y));
  ap_ignore_A: assert property ((S === 1'b1 && $changed(A) && !$changed(S) && !$changed(B)) |-> ##0 !$changed(Y));

  // X/Z handling
  ap_x_when_sel_x_and_inputs_diff: assert property (((S !== 1'b0) && (S !== 1'b1) && (A !== B)) |-> Y === 1'bx);
  ap_known_when_sel0_and_A_known: assert property ((S === 1'b0 && !$isunknown(A)) |-> (!$isunknown(Y) && Y === A));
  ap_known_when_sel1_and_B_known: assert property ((S === 1'b1 && !$isunknown(B)) |-> (!$isunknown(Y) && Y === B));

  // Coverage
  cv_sel0_follow:        cover property (S === 1'b0 && $changed(A) && $changed(Y) && Y === A);
  cv_sel1_follow:        cover property (S === 1'b1 && $changed(B) && $changed(Y) && Y === B);
  cv_sel_toggle_diff_in: cover property ($changed(S) && (A !== B) && $changed(Y));

endmodule

bind mux_2_1 mux_2_1_sva u_mux_2_1_sva (.*);