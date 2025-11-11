// SVA for sky130_fd_sc_ls__xor2
module sky130_fd_sc_ls__xor2_sva (input logic A, B, X);

  // Sample on any change of inputs or output
  default clocking cb @(A or B or X); endclocking

  // Functional correctness (allow delta-cycle for settle)
  ap_truth:       assert property (1 |-> ##0 ( !$isunknown({A,B}) |-> (X === (A ^ B)) ));
  // Output must be known when inputs are known
  ap_no_x_on_out: assert property (1 |-> ##0 ( !$isunknown({A,B}) |-> !$isunknown(X) ));

  // No spurious output changes
  ap_no_spurious: assert property ($changed(X) |-> ($changed(A) || $changed(B)));

  // Single-input toggle must toggle output
  ap_toggle_A:    assert property ($changed(A) && $stable(B) |-> ##0 $changed(X));
  ap_toggle_B:    assert property ($changed(B) && $stable(A) |-> ##0 $changed(X));

  // Coverage: hit all truth-table points
  cv_tt00: cover property (1 |-> ##0 (A==0 && B==0 && X==0));
  cv_tt01: cover property (1 |-> ##0 (A==0 && B==1 && X==1));
  cv_tt10: cover property (1 |-> ##0 (A==1 && B==0 && X==1));
  cv_tt11: cover property (1 |-> ##0 (A==1 && B==1 && X==0));

  // Coverage: observe single-input propagation
  cv_tgl_A: cover property ($changed(A) && $stable(B) ##0 $changed(X));
  cv_tgl_B: cover property ($changed(B) && $stable(A) ##0 $changed(X));

  // Coverage: both inputs change — see both possible outcomes
  cv_both_chg_out_chg: cover property ($changed(A) && $changed(B) ##0 $changed(X));
  cv_both_chg_out_stb: cover property ($changed(A) && $changed(B) ##0 $stable(X));

  // Coverage: output edges
  cv_roseX: cover property ($rose(X));
  cv_fellX: cover property ($fell(X));

endmodule

// Bind into DUT
bind sky130_fd_sc_ls__xor2 sky130_fd_sc_ls__xor2_sva sva (.A(A), .B(B), .X(X));