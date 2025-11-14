// SVA for fsm_pattern_detection
// Bind into DUT to access internal regs directly

module fsm_pattern_detection_sva;

  // Mirror DUT encodings to avoid hierarchy parameters
  localparam bit [1:0] IDLE   = 2'b00;
  localparam bit [1:0] STATE1 = 2'b01;
  localparam bit [1:0] STATE2 = 2'b10;
  localparam bit [2:0] PATTERN= 3'b101;

  // Default clock
  default clocking cb @(posedge clk); endclocking

  // 1) Synchronous reset values (check on the cycle after reset sampled high)
  assert property (reset |=> (state==IDLE && shift_reg==3'b000 && output_reg==1'b0 && detected==1'b0));

  // 2) Output port matches internal reg
  assert property (detected === output_reg);

  // 3) State encoding legal
  assert property (disable iff (reset) state inside {IDLE,STATE1,STATE2});

  // 4) Shift register behavior (skip cycles around reset)
  assert property (disable iff (reset) (!$past(reset)) |-> (shift_reg == { $past(shift_reg[1:0]), $past(data) }));

  // 5) IDLE branch: detect vs no-detect next-state/output
  assert property (disable iff (reset)
                   (state==IDLE && shift_reg==PATTERN) |=> (state==STATE1 && detected==1));
  assert property (disable iff (reset)
                   (state==IDLE && shift_reg!=PATTERN) |=> (state==IDLE   && detected==0));

  // 6) Fixed transitions and outputs from STATE1/STATE2
  assert property (disable iff (reset) (state==STATE1) |=> (state==STATE2 && detected==1));
  assert property (disable iff (reset) (state==STATE2) |=> (state==IDLE   && detected==0));

  // 7) When detected is 1, current state must be STATE1 or STATE2 (no spurious 1s in IDLE)
  assert property (disable iff (reset) detected |-> (state inside {STATE1,STATE2}));

  // 8) Detection pulse is exactly two cycles wide
  assert property (disable iff (reset)
                   ($rose(detected)) |-> (detected ##1 detected ##1 !detected));

  // 9) Basic functional coverages
  cover property (disable iff (reset) $rose(detected));
  cover property (disable iff (reset) state==IDLE ##1 state==STATE1 ##1 state==STATE2 ##1 state==IDLE);
  cover property (disable iff (reset) (state==IDLE && shift_reg==PATTERN) ##1 (state==STATE1) ##1 (state==STATE2));

endmodule

bind fsm_pattern_detection fsm_pattern_detection_sva sva_fsm_pattern_detection();