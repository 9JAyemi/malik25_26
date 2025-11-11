// SVA for sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg
// Function: X = SLEEP_B & A; SLEEP = ~SLEEP_B
module sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva (
  input logic A,
  input logic SLEEP_B,
  input logic X,
  input logic SLEEP
);
  default clocking cb @(posedge A or negedge A or posedge SLEEP_B or negedge SLEEP_B); endclocking

  // Core truth when inputs known
  ap_truth:    assert property (@cb !$isunknown({A,SLEEP_B}) |-> (X === (A & SLEEP_B)));

  // Isolation forces low regardless of A (4-state correct)
  ap_iso_low:  assert property (@cb (SLEEP_B === 1'b0) |-> (X === 1'b0));

  // Pass-through when awake and A known
  ap_pass:     assert property (@cb (SLEEP_B === 1'b1 && !$isunknown(A)) |-> (X === A));

  // No unknown on X when inputs known
  ap_no_x_out: assert property (@cb !$isunknown({A,SLEEP_B}) |-> !$isunknown(X));

  // X cannot be 1 unless both A and SLEEP_B are 1
  ap_one_only_if: assert property (@cb (X === 1'b1) |-> (A === 1'b1 && SLEEP_B === 1'b1));

  // Internal inverter correctness
  ap_sleep_inv: assert property (@cb !$isunknown(SLEEP_B) |-> (SLEEP === ~SLEEP_B));

  // Toggle relations
  ap_a_change_awake:  assert property (@cb (SLEEP_B === 1'b1 && $changed(A))  |-> ##0 $changed(X));
  ap_a_change_asleep: assert property (@cb (SLEEP_B === 1'b0 && $changed(A))  |-> ##0 (!$changed(X) && X === 1'b0));
  ap_slp_fall_forces0:assert property (@cb $fell(SLEEP_B) |-> ##0 (X === 1'b0));
  ap_slp_rise_aligns: assert property (@cb $rose(SLEEP_B) && !$isunknown(A) |-> ##0 (X === A));

  // Coverage
  cp_awake_hi:   cover property (@cb (A===1 && SLEEP_B===1 && X===1));
  cp_awake_lo:   cover property (@cb (A===0 && SLEEP_B===1 && X===0));
  cp_sleep_any:  cover property (@cb (SLEEP_B===0 && X===0));
  cp_rose_s1:    cover property (@cb $rose(SLEEP_B) && A===1 && X===1);
  cp_rose_s0:    cover property (@cb $rose(SLEEP_B) && A===0 && X===0);
  cp_fell:       cover property (@cb $fell(SLEEP_B) && X===0);
  cp_a_tog_awake:cover property (@cb (SLEEP_B===1 && $changed(A) && $changed(X)));
  cp_a_tog_sleep:cover property (@cb (SLEEP_B===0 && $changed(A) && ! $changed(X) && X===0));
endmodule

bind sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg sky130_fd_sc_hvl__lsbuflv2hv_clkiso_hlkg_sva
  u_sva(.A(A), .SLEEP_B(SLEEP_B), .X(X), .SLEEP(SLEEP));