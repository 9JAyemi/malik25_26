module pwm_out_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic        fifo_rdreq,
  input  logic        fifo_empty,
  input  logic [31:0] fifo_data,
  input  logic        pwm_out_l,
  input  logic        pwm_out_r,
  // Internal signals from RTL (bind to these)
  input  logic        data_rdy,
  input  logic [11:0] pwm_timer,
  input  logic [31:0] audiodata_32,
  input  logic [31:0] audiodata_32_p
);

  ///// Reset behavior /////
  // At reset, internal registers are driven to 0.
  check_reset_regs_zero: assert property (
    @(posedge clk) !reset_n |-> (pwm_timer == 12'd0) && (fifo_rdreq == 1'b0) &&
                               (audiodata_32 == 32'd0) && (audiodata_32_p == 32'd0) &&
                               (data_rdy == 1'b0)
  );
  // At reset, PWM outputs are HIGH (timer=0, thresholds=0).
  check_reset_pwm_out_high: assert property (
    @(posedge clk) !reset_n |-> (pwm_out_l == 1'b1) && (pwm_out_r == 1'b1)
  );

  ///// Timer behavior /////
  // pwm_timer increments by 1 every cycle (wraps naturally).
  check_timer_increments: assert property (
    @(posedge clk) disable iff (!reset_n) $past(reset_n) |-> (pwm_timer == $past(pwm_timer) + 12'd1)
  );

  ///// FIFO read request generation /////
  // When timer hits 0x800 and FIFO not empty, rdreq is asserted next cycle.
  check_rdreq_set_at_800: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer == 12'h800 && (fifo_empty == 1'b0)) |-> ##1 (fifo_rdreq == 1'b1)
  );
  // rdreq is observed HIGH only at timer==0x801.
  check_rdreq_high_only_at_801: assert property (
    @(posedge clk) disable iff (!reset_n) (fifo_rdreq == 1'b1) |-> (pwm_timer == 12'h801)
  );
  // A rising rdreq implies previous cycle was 0x800 and FIFO not empty.
  check_rdreq_rise_requires_not_empty_800: assert property (
    @(posedge clk) disable iff (!reset_n) $rose(fifo_rdreq) |-> ($past(pwm_timer) == 12'h800) && ($past(fifo_empty) == 1'b0)
  );
  // rdreq deasserts one cycle after being observed high at 0x801.
  check_rdreq_clear_after_801: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer == 12'h801 && fifo_rdreq == 1'b1) |-> ##1 (fifo_rdreq == 1'b0)
  );
  // rdreq pulse width is exactly one cycle.
  check_rdreq_one_cycle_pulse: assert property (
    @(posedge clk) disable iff (!reset_n) $rose(fifo_rdreq) |-> ##1 (!fifo_rdreq)
  );

  ///// Data capture and ready signaling /////
  // On 0x801 with rdreq high, capture fifo_data into audiodata_32_p next cycle.
  check_capture_data_on_801: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer == 12'h801 && fifo_rdreq == 1'b1) |-> ##1 (audiodata_32_p == $past(fifo_data))
  );
  // On 0x801 with rdreq high, data_rdy is asserted next cycle.
  check_data_rdy_set_after_801: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer == 12'h801 && fifo_rdreq == 1'b1) |-> ##1 (data_rdy == 1'b1)
  );
  // data_rdy stays asserted until timer reaches 0xFFF.
  check_data_rdy_holds_until_fff: assert property (
    @(posedge clk) disable iff (!reset_n) (data_rdy == 1'b1 && pwm_timer != 12'hfff) |-> ##1 (data_rdy == 1'b1)
  );
  // On 0xFFF with data_rdy, data_rdy clears next cycle.
  check_data_rdy_clear_at_fff: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer == 12'hfff && data_rdy == 1'b1) |-> ##1 (data_rdy == 1'b0)
  );
  // On 0xFFF with data_rdy, audiodata_32 updates from audiodata_32_p next cycle.
  check_audiodata32_update_at_fff: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer == 12'hfff && data_rdy == 1'b1) |-> ##1 (audiodata_32 == $past(audiodata_32_p))
  );
  // audiodata_32 only changes following 0xFFF with data_rdy.
  check_audiodata32_changes_only_on_fff: assert property (
    @(posedge clk) disable iff (!reset_n) $changed(audiodata_32) |-> ($past(pwm_timer) == 12'hfff && $past(data_rdy) == 1'b1)
  );
  // audiodata_32_p only changes following 0x801 with rdreq high.
  check_audiodata32p_changes_only_on_801: assert property (
    @(posedge clk) disable iff (!reset_n) $changed(audiodata_32_p) |-> ($past(pwm_timer) == 12'h801 && $past(fifo_rdreq) == 1'b1)
  );

  ///// PWM output combinational correctness /////
  // Left PWM is HIGH when timer <= left threshold.
  check_pwm_out_l_high_when_lte: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer <= audiodata_32[15:4]) |-> (pwm_out_l == 1'b1)
  );
  // Left PWM is LOW when timer > left threshold.
  check_pwm_out_l_low_when_gt: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer > audiodata_32[15:4]) |-> (pwm_out_l == 1'b0)
  );
  // Right PWM is HIGH when timer <= right threshold.
  check_pwm_out_r_high_when_lte: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer <= audiodata_32[31:20]) |-> (pwm_out_r == 1'b1)
  );
  // Right PWM is LOW when timer > right threshold.
  check_pwm_out_r_low_when_gt: assert property (
    @(posedge clk) disable iff (!reset_n) (pwm_timer > audiodata_32[31:20]) |-> (pwm_out_r == 1'b0)
  );
  // Left PWM is known when inputs to comparator are known.
  check_pwm_out_l_known_when_inputs_known: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({pwm_timer, audiodata_32[15:4]})) |-> (!$isunknown(pwm_out_l))
  );
  // Right PWM is known when inputs to comparator are known.
  check_pwm_out_r_known_when_inputs_known: assert property (
    @(posedge clk) disable iff (!reset_n) (!$isunknown({pwm_timer, audiodata_32[31:20]})) |-> (!$isunknown(pwm_out_r))
  );
  // If left/right thresholds are equal, PWM outputs must match.
  check_pwms_equal_when_thresholds_equal: assert property (
    @(posedge clk) disable iff (!reset_n) (audiodata_32[15:4] == audiodata_32[31:20]) |-> (pwm_out_l == pwm_out_r)
  );

endmodule