module fsm_pattern_detection_sva (
  input logic clk,
  input logic reset,
  input logic data,
  input logic detected,
  // Internal signals from DUT (bind hierarchically)
  input logic [1:0] state,
  input logic [2:0] shift_reg,
  input logic output_reg
);
  // Mirror DUT localparams
  localparam IDLE   = 2'b00;
  localparam STATE1 = 2'b01;
  localparam STATE2 = 2'b10;
  localparam PATTERN = 3'b101;

  ///// Basic wiring /////
  // detected must equal output_reg due to continuous assign.
  check_detected_matches_output_reg: assert property (
    @(posedge clk) disable iff (reset) detected == output_reg
  );

  ///// Reset behavior /////
  // On the first cycle out of reset, all regs return to defaults.
  check_reset_release_defaults: assert property (
    @(posedge clk) disable iff (reset) $past(reset) |-> (state == IDLE) && (shift_reg == 3'b000) && (output_reg == 1'b0) && (detected == 1'b0)
  );

  ///// Shift register behavior /////
  // Shift register updates with previous value and previous data.
  check_shift_reg_update: assert property (
    @(posedge clk) disable iff (reset) shift_reg == {$past(shift_reg)[1:0], $past(data)}
  );

  ///// FSM next-state rules /////
  // From IDLE with pattern match, next state is STATE1.
  check_idle_match_next_state: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == IDLE) && ($past(shift_reg) == PATTERN) |-> (state == STATE1)
  );
  // From IDLE without pattern match, stay in IDLE.
  check_idle_nomatch_next_state: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == IDLE) && ($past(shift_reg) != PATTERN) |-> (state == IDLE)
  );
  // From STATE1, next state is STATE2.
  check_state1_next_state: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == STATE1) |-> (state == STATE2)
  );
  // From STATE2, next state is IDLE.
  check_state2_next_state: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == STATE2) |-> (state == IDLE)
  );

  ///// Output behavior /////
  // From IDLE with pattern match, detected asserted next cycle.
  check_idle_match_detected: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == IDLE) && ($past(shift_reg) == PATTERN) |-> (detected == 1'b1)
  );
  // From IDLE without pattern match, detected deasserted next cycle.
  check_idle_nomatch_detected: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == IDLE) && ($past(shift_reg) != PATTERN) |-> (detected == 1'b0)
  );
  // In STATE1, detected is asserted.
  check_state1_detected: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == STATE1) |-> (detected == 1'b1)
  );
  // In STATE2, detected is deasserted.
  check_state2_detected: assert property (
    @(posedge clk) disable iff (reset) ($past(state) == STATE2) |-> (detected == 1'b0)
  );

  ///// Detected pulse shape /////
  // A rising edge of detected is followed by one more HIGH then a LOW.
  check_detected_two_cycle_pulse: assert property (
    @(posedge clk) disable iff (reset) $rose(detected) |-> (##1 detected ##1 !detected)
  );
  // Any rising edge of detected implies prior cycle was IDLE with pattern.
  check_detected_rise_corresponds_to_match: assert property (
    @(posedge clk) disable iff (reset) $rose(detected) |-> ($past(state) == IDLE) && ($past(shift_reg) == PATTERN)
  );

endmodule