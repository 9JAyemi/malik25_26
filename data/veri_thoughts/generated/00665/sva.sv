module fsm_consecutive_ones_detection_sva (
  input logic clk,
  input logic reset,
  input logic [15:0] data,
  input logic [3:0] count,
  input logic [1:0] state,
  input logic [3:0] count_reg
);
  localparam logic [1:0] S0 = 2'b00;
  localparam logic [1:0] S1 = 2'b01;

  // Reset forces state=S0, count_reg=0, and output count=0.
  check_reset_initialization: assert property (
    @(posedge clk) reset |-> (state == S0) && (count_reg == 4'd0) && (count == 4'd0)
  );

  // When in S0, output count must be 0.
  check_output_zero_in_S0: assert property (
    @(posedge clk) disable iff (reset) (state == S0) |-> (count == 4'd0)
  );

  // When in S1, output count equals count_reg.
  check_output_matches_reg_in_S1: assert property (
    @(posedge clk) disable iff (reset) (state == S1) |-> (count == count_reg)
  );

  // From S0 with data==FFFF, next state is S1 with count_reg=1 and output count=1.
  check_S0_to_S1_on_all_ones: assert property (
    @(posedge clk) disable iff (reset) (state == S0 && data == 16'hFFFF) |=> (state == S1 && count_reg == 4'd1 && count == 4'd1)
  );

  // From S0 with data!=FFFF, stay in S0 and clear count_reg and output.
  check_S0_stay_on_not_all_ones: assert property (
    @(posedge clk) disable iff (reset) (state == S0 && data != 16'hFFFF) |=> (state == S0 && count_reg == 4'd0 && count == 4'd0)
  );

  // From S1 with data==FFFF, stay in S1 and increment count_reg and output by 1.
  check_S1_stay_and_increment_on_all_ones: assert property (
    @(posedge clk) disable iff (reset || $initstate) (state == S1 && data == 16'hFFFF) |=> (state == S1 && (count_reg == $past(count_reg) + 4'd1) && (count == $past(count) + 4'd1))
  );

  // From S1 with data!=FFFF, go to S0 and clear count_reg and output.
  check_S1_to_S0_on_not_all_ones: assert property (
    @(posedge clk) disable iff (reset) (state == S1 && data != 16'hFFFF) |=> (state == S0 && count_reg == 4'd0 && count == 4'd0)
  );

  // Remaining in S1 implies previous cycle had data==FFFF.
  check_stay_S1_requires_prev_all_ones: assert property (
    @(posedge clk) disable iff (reset || $initstate) ($past(state) == S1 && state == S1) |-> ($past(data) == 16'hFFFF)
  );

  // Transition S0->S1 implies previous cycle had data==FFFF.
  check_S0_to_S1_requires_prev_all_ones: assert property (
    @(posedge clk) disable iff (reset || $initstate) ($past(state) == S0 && state == S1) |-> ($past(data) == 16'hFFFF)
  );

  // Transition S1->S0 implies previous cycle had data!=FFFF.
  check_S1_to_S0_requires_prev_not_all_ones: assert property (
    @(posedge clk) disable iff (reset || $initstate) ($past(state) == S1 && state == S0) |-> ($past(data) != 16'hFFFF)
  );

endmodule