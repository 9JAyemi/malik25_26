// SVA for mux_2to1_enable
module mux_2to1_enable_sva (input A, input B, input E, input Y);

  // 4-state functional equivalence (handles X/Z correctly)
  ap_func_4state: assert property (@(A or B or E) ##0 (Y === ((E & A) | (~E & B))));

  // No X/Z on Y when all inputs are known
  ap_known_out:   assert property (@(A or B or E) (!$isunknown({A,B,E})) |-> ##0 (!$isunknown(Y)));

  // Independence: unselected input must not affect Y
  ap_indep_B_when_E1: assert property (@(A or B or E)
                                       ($changed(B) && (E === 1'b1) && $stable(E) && $stable(A))
                                       |-> ##0 $stable(Y));
  ap_indep_A_when_E0: assert property (@(A or B or E)
                                       ($changed(A) && (E === 1'b0) && $stable(E) && $stable(B))
                                       |-> ##0 $stable(Y));

  // Coverage
  cp_sel1:       cover property (@(A or B or E) (E === 1'b1) ##0 (Y === A));
  cp_sel0:       cover property (@(A or B or E) (E === 1'b0) ##0 (Y === B));
  cp_x_equal:    cover property (@(A or B or E) ($isunknown(E) && (A === B)) ##0 (Y === A));
  cp_x_diff:     cover property (@(A or B or E) ($isunknown(E) && (A !== B)) ##0 $isunknown(Y));
  cp_A_to_Y:     cover property (@(A or B or E) (E === 1'b1 && $changed(A) && $stable(E)) ##0 ($changed(Y) && (Y === A)));
  cp_B_to_Y:     cover property (@(A or B or E) (E === 1'b0 && $changed(B) && $stable(E)) ##0 ($changed(Y) && (Y === B)));

endmodule

// Bind into DUT
bind mux_2to1_enable mux_2to1_enable_sva i_mux_2to1_enable_sva (.A(A), .B(B), .E(E), .Y(Y));