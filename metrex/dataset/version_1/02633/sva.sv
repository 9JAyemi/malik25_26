// SVA for FSM_INPUT_ENABLE
// Bindable, concise, and checks transitions, outputs, legality, and reset.
// Copy-paste this into an assertions file and bind to the DUT.

module FSM_INPUT_ENABLE_sva #(
  parameter logic [2:0] State0 = 3'd0,
  parameter logic [2:0] State1 = 3'd1,
  parameter logic [2:0] State2 = 3'd2,
  parameter logic [2:0] State3 = 3'd3,
  parameter logic [2:0] State4 = 3'd4,
  parameter logic [2:0] State5 = 3'd5,
  parameter logic [2:0] State6 = 3'd6,
  parameter logic [2:0] State7 = 3'd7
)(
  input logic        clk,
  input logic        rst,
  input logic        init_OPERATION,
  input logic [2:0]  state_reg,
  input logic        enable_input_internal,
  input logic        enable_shift_reg,
  input logic        enable_Pipeline_input
);

  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals
  ap_no_x: assert property (!$isunknown({rst, init_OPERATION, state_reg,
                                         enable_input_internal, enable_shift_reg, enable_Pipeline_input}));

  // Asynchronous reset drives State0 (sampled on clk)
  ap_reset_state0: assert property (rst |-> state_reg == State0);

  // State legality: only S0..S5 reachable
  ap_legal_states: assert property (state_reg inside {State0,State1,State2,State3,State4,State5});

  // Transition relation (independent of init except at S0)
  ap_s0_hold_when_no_init: assert property (disable iff (rst)
    (state_reg==State0 && !init_OPERATION) |=> state_reg==State0);

  ap_s0_to_s1_on_init: assert property (disable iff (rst)
    (state_reg==State0 &&  init_OPERATION) |=> state_reg==State1);

  ap_s1_to_s2: assert property (disable iff (rst)
    state_reg==State1 |=> state_reg==State2);

  ap_s2_to_s3: assert property (disable iff (rst)
    state_reg==State2 |=> state_reg==State3);

  ap_s3_to_s4: assert property (disable iff (rst)
    state_reg==State3 |=> state_reg==State4);

  ap_s4_to_s5: assert property (disable iff (rst)
    state_reg==State4 |=> state_reg==State5);

  ap_s5_to_s0: assert property (disable iff (rst)
    state_reg==State5 |=> state_reg==State0);

  // Exact operation length: 5 cycles from S0+init back to S0 with fixed path
  ap_op_length_and_path: assert property (disable iff (rst)
    (state_reg==State0 && init_OPERATION)
      |=> state_reg==State1
      ##1 state_reg==State2
      ##1 state_reg==State3
      ##1 state_reg==State4
      ##1 state_reg==State5
      ##1 state_reg==State0);

  // Output decoding matches state
  ap_en_int_map:  assert property (enable_input_internal == (state_reg inside {State0,State1,State2}));
  ap_shift_map:   assert property (enable_shift_reg == (state_reg != State0));

  // Combinational relation for pipeline enable
  ap_pipe_eq_and: assert property (enable_Pipeline_input == (enable_input_internal && init_OPERATION));

  // Stronger implied consequence: in S3..S5 pipeline must be 0
  ap_pipe_low_in_S3toS5: assert property (state_reg inside {State3,State4,State5} |-> enable_Pipeline_input==1'b0);

  // Coverage
  cp_full_operation: cover property (disable iff (rst)
    (state_reg==State0 && init_OPERATION)
      ##1 state_reg==State1
      ##1 state_reg==State2
      ##1 state_reg==State3
      ##1 state_reg==State4
      ##1 state_reg==State5
      ##1 state_reg==State0);

  cp_idle_in_s0: cover property (disable iff (rst)
    (state_reg==State0 && !init_OPERATION)[*3]);

  // Back-to-back operations (return to S0 and immediately re-launch)
  cp_back_to_back_ops: cover property (disable iff (rst)
    (state_reg==State0 && init_OPERATION)
      ##6 (state_reg==State0 && init_OPERATION)
      ##1 state_reg==State1);

endmodule

// Bind example (place in a separate file or below the DUT)
bind FSM_INPUT_ENABLE FSM_INPUT_ENABLE_sva #(
  .State0(State0), .State1(State1), .State2(State2), .State3(State3),
  .State4(State4), .State5(State5), .State6(State6), .State7(State7)
) fsm_input_enable_sva_i (
  .clk(clk),
  .rst(rst),
  .init_OPERATION(init_OPERATION),
  .state_reg(state_reg),
  .enable_input_internal(enable_input_internal),
  .enable_shift_reg(enable_shift_reg),
  .enable_Pipeline_input(enable_Pipeline_input)
);