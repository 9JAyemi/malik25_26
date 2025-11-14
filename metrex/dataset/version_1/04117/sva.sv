// SVA for mux_2to1
module mux_2to1_sva (input logic A, B, S, M);

  // Functional equivalence (4-state accurate), sampled after updates
  property p_func;
    @(A or B or S or M) 1 |-> ##0 (M === ((S == 1'b1) ? B : A));
  endproperty
  a_func: assert property (p_func);

  // If inputs are known, output must be known
  a_no_x: assert property (@(A or B or S) (!$isunknown({A,B,S})) |-> ##0 !$isunknown(M));

  // Selected input must drive M when S is stable
  a_follow_A_sel0: assert property (@(A or S) (S === 1'b0 && $stable(S)) |-> ##0 (M === A));
  a_follow_B_sel1: assert property (@(B or S) (S === 1'b1 && $stable(S)) |-> ##0 (M === B));

  // Unselected input must not affect M (guard against simultaneous changes)
  a_ignore_B_when_sel0: assert property (@(B) (S === 1'b0 && $stable(S) && $stable(A)) |-> ##0 $stable(M));
  a_ignore_A_when_sel1: assert property (@(A) (S === 1'b1 && $stable(S) && $stable(B)) |-> ##0 $stable(M));

  // Coverage
  c_sel0_path: cover property (@(A or B or S or M) (S == 1'b0) ##0 (M === A));
  c_sel1_path: cover property (@(A or B or S or M) (S == 1'b1) ##0 (M === B));
  c_s_toggle_changes_M_when_inputs_differ: cover property (@(S) (A !== B) |-> ##0 $changed(M));
  c_selected_input_toggle_changes_M_sel0: cover property (@(A) (S === 1'b0 && $stable(S)) |-> ##0 $changed(M));
  c_selected_input_toggle_changes_M_sel1: cover property (@(B) (S === 1'b1 && $stable(S)) |-> ##0 $changed(M));

endmodule

bind mux_2to1 mux_2to1_sva i_mux_2to1_sva (.*);