// SVA for fsm_4state_sequence_detection
// Bind into DUT to check transitions, outputs, one-hot, gating, and coverage.

module fsm_4state_sequence_detection_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        data,
  input  logic        enable,
  input  logic        match,
  input  logic [3:0]  state_reg,
  input  logic        output_reg
);
  // Mirror encoding (matches DUT params)
  localparam logic [3:0] A = 4'b0001;
  localparam logic [3:0] B = 4'b0010;
  localparam logic [3:0] C = 4'b0100;
  localparam logic [3:0] D = 4'b1000;

  // Basic structural checks
  a_no_xz:        assert property (@(posedge clk) !$isunknown({state_reg,output_reg,match}));
  a_onehot_state: assert property (@(posedge clk) $onehot(state_reg));
  a_match_bind:   assert property (@(posedge clk) match == output_reg);

  // Reset behavior (synchronous)
  a_reset_next:   assert property (@(posedge clk) reset |=> (state_reg==A && output_reg==1'b0 && match==1'b0));

  // Gating: hold state and output when enable==0
  a_hold_when_disabled:
    assert property (@(posedge clk) disable iff (reset)
      !enable |=> (state_reg==$past(state_reg) && output_reg==$past(output_reg)));

  // Transition checks (enable==1)
  a_A_d1_to_B: assert property (@(posedge clk) disable iff (reset) (enable && state_reg==A &&  data) |=> state_reg==B);
  a_A_d0_to_A: assert property (@(posedge clk) disable iff (reset) (enable && state_reg==A && !data) |=> state_reg==A);

  a_B_d0_to_C: assert property (@(posedge clk) disable iff (reset) (enable && state_reg==B && !data) |=> state_reg==C);
  a_B_d1_to_B: assert property (@(posedge clk) disable iff (reset) (enable && state_reg==B &&  data) |=> state_reg==B);

  a_C_d1_to_D: assert property (@(posedge clk) disable iff (reset) (enable && state_reg==C &&  data) |=> state_reg==D);
  a_C_d0_to_A: assert property (@(posedge clk) disable iff (reset) (enable && state_reg==C && !data) |=> state_reg==A);

  a_D_d0_to_A_and_set_out:
    assert property (@(posedge clk) disable iff (reset) (enable && state_reg==D && !data) |=> (state_reg==A && output_reg==1'b1));
  a_D_d1_to_B:
    assert property (@(posedge clk) disable iff (reset) (enable && state_reg==D &&  data) |=> state_reg==B);

  // Output constraints
  // Only rises due to D with data==0 on the prior cycle; then stays 1 until reset
  a_out_rise_cause:
    assert property (@(posedge clk) disable iff (reset) $rose(output_reg) |-> $past(enable && state_reg==D && !data));
  a_out_sticky_until_reset:
    assert property (@(posedge clk) disable iff (reset) $rose(output_reg) |-> output_reg until_with reset);
  // No change to output in other enabled transitions
  a_out_no_change_else:
    assert property (@(posedge clk) disable iff (reset)
      (enable && !(state_reg==D && !data)) |=> output_reg==$past(output_reg));

  // Coverage
  c_reach_A: cover property (@(posedge clk) state_reg==A);
  c_reach_B: cover property (@(posedge clk) state_reg==B);
  c_reach_C: cover property (@(posedge clk) state_reg==C);
  c_reach_D: cover property (@(posedge clk) state_reg==D);

  // Cover the full 1,0,1,0 detection sequence that sets match/output_reg
  c_detect_seq_and_match:
    cover property (@(posedge clk) disable iff (reset)
      state_reg==A ##1
      (enable &&  data) ##1
      (enable && !data) ##1
      (enable &&  data) ##1
      (enable && !data && $rose(output_reg)));
endmodule

bind fsm_4state_sequence_detection fsm_4state_sequence_detection_sva sva (.*);