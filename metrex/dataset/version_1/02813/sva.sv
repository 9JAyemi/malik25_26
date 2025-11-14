// SVA for d_flip_flop_reset_set
module d_flip_flop_reset_set_sva (
  input logic CLK,
  input logic D,
  input logic RESET_B,
  input logic SET_B,
  input logic Q,
  input logic Q_N
);

  default clocking cb @(posedge CLK); endclocking

  // Priority and functional correctness (post-NBA via ##0)
  ap_reset_dominates: assert property (!RESET_B |-> ##0 (Q===1'b0 && Q_N===1'b1));
  ap_set_only:        assert property ( RESET_B && !SET_B |-> ##0 (Q===1'b1 && Q_N===1'b0));
  ap_capture:         assert property ( RESET_B &&  SET_B |-> ##0 (Q===D     && Q_N===~D));

  // Outputs always complementary
  ap_complement:      assert property (##0 (Q_N === ~Q));

  // No glitches between clocks (registered outputs change only on posedge)
  ap_no_glitch:       assert property (@(negedge CLK) $stable(Q) && $stable(Q_N));

  // Coverage: exercise all modes and key transitions
  cv_reset:           cover  property (!RESET_B ##0 (Q===1'b0 && Q_N===1'b1));
  cv_set:             cover  property ( RESET_B && !SET_B ##0 (Q===1'b1 && Q_N===1'b0));
  cv_cap0:            cover  property ( RESET_B &&  SET_B && D===1'b0 ##0 (Q===1'b0 && Q_N===1'b1));
  cv_cap1:            cover  property ( RESET_B &&  SET_B && D===1'b1 ##0 (Q===1'b1 && Q_N===1'b0));
  cv_both_low:        cover  property (!RESET_B && !SET_B ##0 (Q===1'b0 && Q_N===1'b1)); // reset wins
  cv_set_to_reset:    cover  property ((RESET_B && !SET_B) ##1 (!RESET_B));
  cv_reset_to_set:    cover  property ((!RESET_B) ##1 (RESET_B && !SET_B));
  cv_d_toggle:        cover  property ( RESET_B && SET_B && $changed(D));

endmodule

// Bind to DUT
bind d_flip_flop_reset_set d_flip_flop_reset_set_sva u_sva (
  .CLK(CLK),
  .D(D),
  .RESET_B(RESET_B),
  .SET_B(SET_B),
  .Q(Q),
  .Q_N(Q_N)
);