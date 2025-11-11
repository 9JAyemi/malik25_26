// SVA for sky130_fd_sc_ls__and2b
module sky130_fd_sc_ls__and2b_sva (
  input logic A_N,
  input logic B,
  input logic X
);

  // Functional equivalence (4-state), allow delta-cycle settle after any change
  a_func: assert property (@(A_N or B or X) 1'b1 |-> ##0 (X === (~A_N & B)));

  // No spurious output change without an input change
  a_no_spurious: assert property (@(A_N or B or X) $changed(X) |-> ($changed(A_N) || $changed(B)));

  // Known output when inputs are known
  a_known_out: assert property (@(A_N or B or X) !$isunknown({A_N,B}) |-> ##0 !$isunknown(X));

  // Useful pin-fix implications (redundant with a_func but good diagnostics)
  a_B0:  assert property (@(A_N or B or X) (B   === 1'b0) |-> ##0 (X === 1'b0));
  a_AN1: assert property (@(A_N or B or X) (A_N === 1'b1) |-> ##0 (X === 1'b0));
  a_AN0: assert property (@(A_N or B or X) (A_N === 1'b0) |-> ##0 (X === B));
  a_B1:  assert property (@(A_N or B or X) (B   === 1'b1) |-> ##0 (X === ~A_N));

  // Coverage: all input combinations with expected output, plus toggles
  c_00: cover property (@(A_N or B or X) ##0 (A_N===1'b0 && B===1'b0 && X===1'b0));
  c_01: cover property (@(A_N or B or X) ##0 (A_N===1'b0 && B===1'b1 && X===1'b1));
  c_10: cover property (@(A_N or B or X) ##0 (A_N===1'b1 && B===1'b0 && X===1'b0));
  c_11: cover property (@(A_N or B or X) ##0 (A_N===1'b1 && B===1'b1 && X===1'b0));

  c_toggle_X:      cover property (@(A_N or B or X) $changed(X));
  c_toggle_inputs: cover property (@(A_N or B or X) $changed(A_N) && $changed(B));

endmodule

// Bind into DUT
bind sky130_fd_sc_ls__and2b sky130_fd_sc_ls__and2b_sva sva_i (.A_N(A_N), .B(B), .X(X));