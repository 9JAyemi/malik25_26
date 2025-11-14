// SVA for CHANNEL_ERROR_DETECT
// Concise, quality-focused properties with functional coverage.
// Uses ##0 to sample post-NBA values; gates first-cycle effects via past_valid.

bind CHANNEL_ERROR_DETECT CHANNEL_ERROR_DETECT_SVA sva_CHANNEL_ERROR_DETECT();

module CHANNEL_ERROR_DETECT_SVA;

  default clocking cb @(posedge USER_CLK); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(cb) past_valid <= 1'b1;

  // Combinational relations
  ap_soft_comb: assert property (past_valid |-> ##0 (channel_soft_error_c == (soft_error_r[0] | soft_error_r[1])));
  ap_hard_comb: assert property (past_valid |-> ##0 (channel_hard_error_c == hard_error_r));
  ap_reset_comb: assert property (##0 (reset_channel_c == !LANE_UP));

  // Register capture
  ap_soft_capture: assert property (past_valid |-> ##0 (soft_error_r == $past(SOFT_ERROR)));
  ap_hard_capture: assert property (past_valid |-> ##0 (hard_error_r == $past(HARD_ERROR)));

  // Output mapping (1-cycle latency from inputs)
  ap_soft_out_map: assert property (past_valid |-> ##0 (CHANNEL_SOFT_ERROR == $past(SOFT_ERROR[0] | SOFT_ERROR[1])));
  ap_hard_out_map: assert property (past_valid |-> ##0 (CHANNEL_HARD_ERROR == $past(HARD_ERROR)));
  ap_reset_out_map: assert property (past_valid |-> ##0 (RESET_CHANNEL == $past((!LANE_UP) | POWER_DOWN)));

  // No X-propagation after first clock
  ap_no_x_regs: assert property (past_valid |-> ##0 (!$isunknown(soft_error_r) && !$isunknown(hard_error_r)));
  ap_no_x_outs: assert property (past_valid |-> ##0 (!$isunknown(CHANNEL_SOFT_ERROR) && !$isunknown(CHANNEL_HARD_ERROR) && !$isunknown(RESET_CHANNEL)));

  // Functional coverage
  // Soft-error effects
  cv_soft_lane0_sets: cover property (past_valid && SOFT_ERROR[0] ##1 CHANNEL_SOFT_ERROR);
  cv_soft_lane1_sets: cover property (past_valid && SOFT_ERROR[1] ##1 CHANNEL_SOFT_ERROR);
  cv_soft_clear:      cover property (past_valid && !(SOFT_ERROR[0] | SOFT_ERROR[1]) ##1 !CHANNEL_SOFT_ERROR);

  // Hard-error effects
  cv_hard_set:        cover property (past_valid && HARD_ERROR ##1 CHANNEL_HARD_ERROR);
  cv_hard_clear:      cover property (past_valid && !HARD_ERROR ##1 !CHANNEL_HARD_ERROR);

  // Reset behavior (all key combinations)
  cv_reset_deassert:  cover property (past_valid && (LANE_UP && !POWER_DOWN) ##1 !RESET_CHANNEL);
  cv_reset_lane_down: cover property (past_valid && (!LANE_UP && !POWER_DOWN) ##1 RESET_CHANNEL);
  cv_reset_pwrdn:     cover property (past_valid && POWER_DOWN ##1 RESET_CHANNEL);

  // Output toggles
  cv_soft_out_01:     cover property (past_valid && !$past(CHANNEL_SOFT_ERROR) ##1 CHANNEL_SOFT_ERROR);
  cv_soft_out_10:     cover property (past_valid &&  $past(CHANNEL_SOFT_ERROR) ##1 !CHANNEL_SOFT_ERROR);

  cv_hard_out_01:     cover property (past_valid && !$past(CHANNEL_HARD_ERROR) ##1 CHANNEL_HARD_ERROR);
  cv_hard_out_10:     cover property (past_valid &&  $past(CHANNEL_HARD_ERROR) ##1 !CHANNEL_HARD_ERROR);

  cv_reset_out_01:    cover property (past_valid && !$past(RESET_CHANNEL) ##1 RESET_CHANNEL);
  cv_reset_out_10:    cover property (past_valid &&  $past(RESET_CHANNEL) ##1 !RESET_CHANNEL);

endmodule