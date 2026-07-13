module fsm_traffic_light_control_sva (
  input logic clock,
  input logic reset,
  input logic pedestrian_crossing_button,
  input logic green_light,
  input logic yellow_light,
  input logic red_light,
  input logic [1:0] state,
  input logic [1:0] next_state
);
  // State encodings (match RTL)
  localparam logic [1:0] S0 = 2'b00;
  localparam logic [1:0] S1 = 2'b01;
  localparam logic [1:0] S2 = 2'b10;
  localparam logic [1:0] S3 = 2'b11;

  // Synchronous reset forces state to S0.
  reset_forces_S0: assert property (
    @(posedge clock) reset |-> (state == S0)
  );

  // When not in reset on consecutive cycles, state updates from prior next_state.
  state_updates_from_next_nonreset: assert property (
    @(posedge clock) disable iff (reset) !$past(reset) |-> (state == $past(next_state))
  );

  // Output decode in S0: green=1, yellow=0, red=0.
  outputs_decode_S0: assert property (
    @(posedge clock) disable iff (reset) (state == S0) |-> (green_light == 1'b1 && yellow_light == 1'b0 && red_light == 1'b0)
  );

  // Output decode in S1: green=0, yellow=1, red=0.
  outputs_decode_S1: assert property (
    @(posedge clock) disable iff (reset) (state == S1) |-> (green_light == 1'b0 && yellow_light == 1'b1 && red_light == 1'b0)
  );

  // Output decode in S2: green=0, yellow=0, red=1.
  outputs_decode_S2: assert property (
    @(posedge clock) disable iff (reset) (state == S2) |-> (green_light == 1'b0 && yellow_light == 1'b0 && red_light == 1'b1)
  );

  // Output decode in S3: green=0, yellow=1, red=0.
  outputs_decode_S3: assert property (
    @(posedge clock) disable iff (reset) (state == S3) |-> (green_light == 1'b0 && yellow_light == 1'b1 && red_light == 1'b0)
  );

  // Lights are mutually exclusive (no two ON simultaneously).
  check_lights_mutex: assert property (
    @(posedge clock) disable iff (reset) !(green_light && yellow_light) && !(green_light && red_light) && !(yellow_light && red_light)
  );

  // Combinational next_state in S0 with no pedestrian: stay in S0.
  comb_next_S0_no_ped: assert property (
    @(posedge clock) disable iff (reset) (state == S0 && pedestrian_crossing_button == 1'b0) |-> (next_state == S0)
  );

  // Combinational next_state in S0 with pedestrian: go to S1.
  comb_next_S0_with_ped: assert property (
    @(posedge clock) disable iff (reset) (state == S0 && pedestrian_crossing_button == 1'b1) |-> (next_state == S1)
  );

  // Combinational next_state in S1: go to S2.
  comb_next_S1_to_S2: assert property (
    @(posedge clock) disable iff (reset) (state == S1) |-> (next_state == S2)
  );

  // Combinational next_state in S2: go to S3.
  comb_next_S2_to_S3: assert property (
    @(posedge clock) disable iff (reset) (state == S2) |-> (next_state == S3)
  );

  // Combinational next_state in S3: go to S0.
  comb_next_S3_to_S0: assert property (
    @(posedge clock) disable iff (reset) (state == S3) |-> (next_state == S0)
  );

  // Sequential transition: from S0 with no pedestrian, remain in S0 next cycle unless reset.
  trans_S0_ped0_stay: assert property (
    @(posedge clock) disable iff (reset) (state == S0 && pedestrian_crossing_button == 1'b0) |-> ##1 (reset || state == S0)
  );

  // Sequential transition: from S0 with pedestrian, go to S1 next cycle unless reset.
  trans_S0_ped1_to_S1: assert property (
    @(posedge clock) disable iff (reset) (state == S0 && pedestrian_crossing_button == 1'b1) |-> ##1 (reset || state == S1)
  );

  // Sequential transition: S1 goes to S2 next cycle unless reset.
  trans_S1_to_S2: assert property (
    @(posedge clock) disable iff (reset) (state == S1) |-> ##1 (reset || state == S2)
  );

  // Sequential transition: S2 goes to S3 next cycle unless reset.
  trans_S2_to_S3: assert property (
    @(posedge clock) disable iff (reset) (state == S2) |-> ##1 (reset || state == S3)
  );

  // Sequential transition: S3 goes to S0 next cycle unless reset.
  trans_S3_to_S0: assert property (
    @(posedge clock) disable iff (reset) (state == S3) |-> ##1 (reset || state == S0)
  );

endmodule