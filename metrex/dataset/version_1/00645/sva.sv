// SVA for shift_register_control
// Bindable module that checks/reset, FSM transitions, counters, shift/update, and output behavior.
// Concise but covers all critical functionality.

module shift_register_control_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  input_value,
  input logic [15:0] output_value,
  input logic [1:0]  state,
  input logic [3:0]  shift_reg,
  input logic [3:0]  pattern,
  input logic [3:0]  count
);
  localparam logic [1:0] IDLE            = 2'b00;
  localparam logic [1:0] WAIT_PATTERN    = 2'b01;
  localparam logic [1:0] OUTPUT_ENABLED  = 2'b10;

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (checked during reset)
  ap_reset: assert property (@(posedge clk)
    reset |-> (state==IDLE && shift_reg==4'd0 && count==4'd0 && output_value==16'd0));

  // Pattern constant
  ap_pattern_const: assert property (@(posedge clk) pattern == 4'b0101);

  // Legal state encoding
  ap_state_legal: assert property (@(posedge clk) disable iff (reset)
    state inside {IDLE, WAIT_PATTERN, OUTPUT_ENABLED});

  // IDLE behavior
  ap_idle_stutter: assert property (@(posedge clk) disable iff (reset)
    (state==IDLE && input_value!=pattern) |=> (state==IDLE));
  ap_idle_to_wait: assert property (@(posedge clk) disable iff (reset)
    (state==IDLE && input_value==pattern) |=> (state==WAIT_PATTERN));
  ap_idle_regs_hold: assert property (@(posedge clk) disable iff (reset)
    (state==IDLE) |=> ($stable(count) && $stable(shift_reg)));

  // WAIT_PATTERN behavior and priority
  ap_wait_break: assert property (@(posedge clk) disable iff (reset)
    (state==WAIT_PATTERN && input_value!=pattern) |=> (state==IDLE && count==4'd0 && shift_reg==4'd0));
  ap_wait_to_output: assert property (@(posedge clk) disable iff (reset)
    (state==WAIT_PATTERN && input_value==pattern && count==4'd3) |=> (state==OUTPUT_ENABLED && count==4'd0));
  ap_wait_progress: assert property (@(posedge clk) disable iff (reset)
    (state==WAIT_PATTERN && input_value==pattern && count!=4'd3 && $past(!reset)) |=> 
      (state==WAIT_PATTERN && count==$past(count)+1 && $stable(shift_reg)));

  // OUTPUT_ENABLED behavior
  // Note: Given RTL, shift_reg loads previous input_value (concatenation truncation)
  ap_out_advance: assert property (@(posedge clk) disable iff (reset)
    (state==OUTPUT_ENABLED && count!=4'd3 && $past(!reset)) |=> 
      (state==OUTPUT_ENABLED && count==$past(count)+1 && shift_reg==$past(input_value)));
  ap_out_done: assert property (@(posedge clk) disable iff (reset)
    (state==OUTPUT_ENABLED && count==4'd3) |=> (state==IDLE && count==4'd0 && shift_reg==4'd0));

  // Counter never exceeds 3
  ap_count_range: assert property (@(posedge clk) disable iff (reset) count <= 4'd3);

  // Shift only allowed in OUTPUT_ENABLED
  ap_shift_only_in_oe: assert property (@(posedge clk) disable iff (reset)
    (state!=OUTPUT_ENABLED) |=> $stable(shift_reg));

  // Output behavior uses previous cycle's state and shift_reg
  ap_out_val_on_prev_state: assert property (@(posedge clk) disable iff (reset)
    ($past(!reset) && $past(state)==OUTPUT_ENABLED) |-> (output_value=={$past(shift_reg),12'b0}));
  ap_out_val_zero_else: assert property (@(posedge clk) disable iff (reset)
    ($past(!reset) && $past(state)!=OUTPUT_ENABLED) |-> (output_value==16'd0));

  // Basic functional coverage
  // Pattern held long enough to enter OUTPUT_ENABLED
  cp_detect_to_output: cover property (@(posedge clk) disable iff (reset)
    (state==IDLE && input_value==pattern)
    ##1 (state==WAIT_PATTERN && input_value==pattern && count==4'd1)
    ##1 (state==WAIT_PATTERN && input_value==pattern && count==4'd2)
    ##1 (state==WAIT_PATTERN && input_value==pattern && count==4'd3)
    ##1 (state==OUTPUT_ENABLED && count==4'd0));

  // OUTPUT_ENABLED run then terminate
  cp_oe_run_and_exit: cover property (@(posedge clk) disable iff (reset)
    (state==OUTPUT_ENABLED && count==4'd1)
    ##1 (state==OUTPUT_ENABLED && count==4'd2)
    ##1 (state==OUTPUT_ENABLED && count==4'd3)
    ##1 (state==IDLE && count==4'd0));

  // Abort path from WAIT_PATTERN on mismatch
  cp_wait_abort: cover property (@(posedge clk) disable iff (reset)
    (state==WAIT_PATTERN && input_value!=pattern) ##1 (state==IDLE && count==4'd0 && shift_reg==4'd0));
endmodule

// Bind into the DUT
bind shift_register_control shift_register_control_sva sva_inst (.*);