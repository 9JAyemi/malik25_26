// SVA checker for mig_7series_v4_0_poc_meta
// Bind this module to the DUT to verify internal behavior.
// Focused, high-signal-quality checks plus targeted coverage.

module mig_7series_v4_0_poc_meta_sva
  #(parameter SCANFROMRIGHT = 0,
    parameter TCQ           = 100,
    parameter TAPCNTRWIDTH  = 7,
    parameter TAPSPERKCLK   = 112);

  // Drive from DUT clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Local constants (sized to match DUT arithmetic)
  localparam [TAPCNTRWIDTH-1:0]    BASE_TW  = TAPSPERKCLK;
  localparam [TAPCNTRWIDTH+1:0]    BASE2_TW = TAPSPERKCLK*2;

  // 0) Signal sanity (no X/Z after reset released)
  assert property (!$isunknown({mmcm_edge_detect_done, run_ends, edge_center, left, right, window_center, diff, poc_backup, mmcm_lbclk_edge_aligned})))
    else $error("X/Z detected on outputs");

  // 1) Synchronizers/pipelines
  assert property (run_end_r  == $past(run_end));
  assert property (run_end_r1 == $past(run_end_r));
  assert property (run_end_r2 == $past(run_end_r1));
  assert property (run_end_r3 == $past(run_end_r2));

  assert property (run_too_small_r1 == $past(run_too_small && (run_ends_r == 2'd1)));
  assert property (run_too_small_r2 == $past(run_too_small_r1));
  assert property (run_too_small_r3 == $past(run_too_small_r2));

  // 2) run_polarity holding behavior
  assert property (run_end |=> run_polarity_held_r == $past(run_polarity)))
    else $error("run_polarity_held_r not loaded on run_end");
  assert property (!run_end |=> run_polarity_held_r == $past(run_polarity_held_r)))
    else $error("run_polarity_held_r not held when no run_end");

  // 3) reset_run_ends and run_ends FSM
  assert property (reset_run_ends |=> run_ends == 2'b00))
    else $error("run_ends not cleared by reset_run_ends");

  // From 00
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b00 && $past(run_end_r3 && run_polarity_held_r) |=> run_ends==2'b01))
    else $error("run_ends 00->01 transition failed");
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b00 && !$past(run_end_r3 && run_polarity_held_r) |=> run_ends==2'b00))
    else $error("run_ends 00 hold failed");

  // From 01
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b01 && $past(run_end_r3) |=> run_ends==2'b10))
    else $error("run_ends 01->10 transition failed");
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b01 && !$past(run_end_r3) |=> run_ends==2'b01))
    else $error("run_ends 01 hold failed");

  // From 10
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b10 && $past(run_end_r3) |=> run_ends==2'b11))
    else $error("run_ends 10->11 transition failed");
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b10 && !$past(run_end_r3) |=> run_ends==2'b10))
    else $error("run_ends 10 hold failed");

  // From 11 (sticky until reset)
  assert property (!$past(reset_run_ends) && $past(run_ends)==2'b11 |=> run_ends==2'b11))
    else $error("run_ends 11 not sticky");

  // 4) done generation
  assert property (done_ns == (mmcm_edge_detect_rdy && (&run_ends_r))))
    else $error("done_ns incorrect");
  assert property (done_r == $past(done_ns)))
    else $error("done_r not registered");
  assert property (mmcm_edge_detect_done == done_r))
    else $error("mmcm_edge_detect_done mismatch");

  // 5) offsets direction
  generate
    if (SCANFROMRIGHT==1) begin
      assert property (offsets == ninety_offsets))
        else $error("offsets mismatch (SCANFROMRIGHT=1)");
    end else begin
      assert property ((offsets + ninety_offsets) == 2'b00))
        else $error("offsets mismatch (SCANFROMRIGHT=0)");
    end
  endgenerate

  // 6) Offset regs and edge diff
  assert property (rise_lead_center_offset_r  == $past(rise_lead_center_offset_ns));
  assert property (rise_trail_center_offset_r == $past(rise_trail_center_offset_ns));

  assert property (edge_diff_ns ==
                   ((rise_trail_center_offset_r >= rise_lead_center_offset_r)
                     ? (rise_trail_center_offset_r - rise_lead_center_offset_r)
                     : (rise_trail_center_offset_r + BASE_TW - rise_lead_center_offset_r))))
    else $error("edge_diff_ns mismatch");
  assert property (edge_diff_r == $past(edge_diff_ns)));

  // 7) edge_center (center function) and register
  assert property (edge_center_ns ==
                   ((({rise_lead_center_offset_r,1'b0} + edge_diff_r) < BASE2_TW)
                      ? ({rise_lead_center_offset_r,1'b0} + edge_diff_r)
                      : ({rise_lead_center_offset_r,1'b0} + edge_diff_r - BASE2_TW))))
    else $error("edge_center_ns mismatch");
  assert property (edge_center_r == $past(edge_center_ns)));
  assert property (edge_center < BASE2_TW))
    else $error("edge_center out of range");

  // 8) left/right selection
  assert property (left  == (use_noise_window ? rise_lead_left  : rise_trail_left)))
    else $error("left mux mismatch");
  assert property (right == (use_noise_window ? rise_trail_right : rise_lead_right)))
    else $error("right mux mismatch");

  // 9) window center path
  assert property (center_diff_r == $past(((right >= left) ? (right - left) : (right + BASE_TW - left)))));
  assert property (window_center_ns ==
                   ((({left,1'b0} + center_diff_r) < BASE2_TW)
                      ? ({left,1'b0} + center_diff_r)
                      : ({left,1'b0} + center_diff_r - BASE2_TW))))
    else $error("window_center_ns mismatch");
  assert property (window_center_r == $past(window_center_ns)));
  assert property (window_center < BASE2_TW))
    else $error("window_center out of range");

  // 10) diff and abs_diff
  assert property (diff_ns ==
                   ((({1'b0, (SCANFROMRIGHT ? edge_center_r   : window_center_r)} >=
                       {1'b0, (SCANFROMRIGHT ? window_center_r : edge_center_r)}))
                      ? ({1'b0, (SCANFROMRIGHT ? edge_center_r   : window_center_r)} -
                         {1'b0, (SCANFROMRIGHT ? window_center_r : edge_center_r)})
                      : ({1'b0, (SCANFROMRIGHT ? edge_center_r   : window_center_r)} +
                         BASE2_TW -
                         {1'b0, (SCANFROMRIGHT ? window_center_r : edge_center_r)}))))
    else $error("diff_ns mismatch");
  assert property (diff_r == $past(diff_ns)));
  assert property (diff == diff_r));
  assert property (diff < BASE2_TW))
    else $error("diff out of range");

  assert property (abs_diff ==
                   ((diff_r > (BASE2_TW >> 1)) ? (BASE2_TW - diff_r) : diff_r)))
    else $error("abs_diff mismatch");

  // 11) prev capture only when done_ns=1
  assert property (done_ns |=> prev_r == $past(diff_r)))
    else $error("prev_r not updated on done_ns");
  assert property (!done_ns |=> prev_r == $past(prev_r)))
    else $error("prev_r changed without done_ns");

  // 12) centering and diffs_eq memory
  assert property (centering == !(ktap_at_right_edge || ktap_at_left_edge));
  assert property (diffs_eq == (abs_diff == diff_r)));

  assert property (!centering |=> diffs_eq_r == 1'b0))
    else $error("diffs_eq_r not cleared when not centering");
  assert property (centering && (done_r && done_ns) |=> diffs_eq_r == $past(diffs_eq)))
    else $error("diffs_eq_r not loaded on back-to-back done");
  assert property (centering && !(done_r && done_ns) |=> diffs_eq_r == $past(diffs_eq_r)))
    else $error("diffs_eq_r not held");

  // 13) edge alignment and outputs
  assert property ((centering && done_ns) |=> edge_aligned_r == ((~|diff_r) || (~diffs_eq && diffs_eq_r))))
    else $error("edge_aligned_r mismatch when qualifying");
  assert property (!(centering && done_ns) |=> edge_aligned_r == 1'b0))
    else $error("edge_aligned_r should be 0 when not qualifying");

  assert property (mmcm_lbclk_edge_aligned == edge_aligned_r))
    else $error("mmcm_lbclk_edge_aligned mismatch");

  assert property (poc_backup == $past( (centering && done_ns && ((~|diff_r) || (~diffs_eq && diffs_eq_r))) &&
                                        (abs_diff > prev_r) )))
    else $error("poc_backup mismatch");

  // 14) Coverage
  cover property (run_ends == 2'b01);
  cover property (run_ends == 2'b10);
  cover property (run_ends == 2'b11 && mmcm_edge_detect_rdy);
  cover property (done_r);

  cover property (centering && done_ns && (diff_r == {($bits(diff_r)){1'b0}}) ##1 mmcm_lbclk_edge_aligned);
  cover property (centering && done_ns && (~diffs_eq && diffs_eq_r) ##1 mmcm_lbclk_edge_aligned);

  cover property ($rose(mmcm_lbclk_edge_aligned) && $past(abs_diff) > $past(prev_r) && poc_backup);

  generate
    if (SCANFROMRIGHT==0) begin
      cover property ((offsets + ninety_offsets) == 2'b00);
    end
  endgenerate

endmodule

// Bind the checker into the DUT
bind mig_7series_v4_0_poc_meta
  mig_7series_v4_0_poc_meta_sva #(
    .SCANFROMRIGHT(SCANFROMRIGHT),
    .TCQ(TCQ),
    .TAPCNTRWIDTH(TAPCNTRWIDTH),
    .TAPSPERKCLK(TAPSPERKCLK)
  ) mig_7series_v4_0_poc_meta_sva_i();