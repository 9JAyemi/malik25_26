module seq_detector_sva (
  input logic clk,
  input logic in,
  output logic out
);
  parameter state0 = 2'b00; // initial state
  parameter state1 = 2'b01; // intermediate state
  parameter state2 = 2'b10; // final state

  reg [1:0] state;

  // Define transitions between states
  always @(*) begin
    case (state)
      state0: if (in == 1'b0) next_state <= state0; else next_state <= state1;
      state1: if (in == 1'b0) next_state <= state0; else next_state <= state2;
      state2: if (in == 1'b0) next_state <= state0; else next_state <= state2;
      default: next_state <= state0;
    endcase
  end

  // Update state
  always @(posedge clk) begin
    state <= next_state;
  end

  // Define output signal
  always @(*) begin
    out = (state == state2);
  end

  // Reset state
  initial begin
    state <= state0;
  end

  // Assertions
  // State transition from state0 to state1
  state_transition_1: assert property (
    @(posedge clk) disable iff (!clk) $rose(in) |-> (state == state0) |-> (next_state == state1)
  );

  // State transition from state1 to state2
  state_transition_2: assert property (
    @(posedge clk) disable iff (!clk) $rose(in) |-> (state == state1) |-> (next_state == state2)
  );

  // State transition from state2 to state0
  state_transition_3: assert property (
    @(posedge clk) disable iff (!clk) $rose(in) |-> (state == state2) |-> (next_state == state0)
  );

  // Output is high when in is high and state is state2
  output_high: assert property (
    @(posedge clk) disable iff (!clk) in |-> (state == state2) |-> (out == 1'b1)
  );

  // Output is low when in is low
  output_low: assert property (
    @(posedge clk) disable iff (!clk) !in |-> (out == 1'b0)
  );

  // State does not transition when in is low
  no_transition: assert property (
    @(posedge clk) disable iff (!clk) !in |-> (state == next_state)
  );

  // State transitions only on rising edge of in
  transition_on_in: assert property (
    @(posedge clk) disable iff (!clk) $rose(in) |-> (state != next_state)
  );

  // State transitions only on falling edge of in
  transition_on_in_fall: assert property (
    @(posedge clk) disable iff (!clk) $fell(in) |-> (state != next_state)
  );

  // State transitions only on rising edge of clk
  transition_on_clk: assert property (
    @(posedge clk) disable iff (!clk) $rose(clk) |-> (state != next_state)
  );

  // State transitions only on falling edge of clk
  transition_on_clk_fall: assert property (
    @(posedge clk) disable iff (!clk) $fell(clk) |-> (state != next_state)
  );

  // State transitions only on rising edge of in and clk
  transition_on_in_clk: assert property (
    @(posedge clk) disable iff (!clk) $rose(in) && $rose(clk) |-> (state != next_state)
  );

  // State transitions only on falling edge of in and clk
  transition_on_in_clk_fall: assert property (
    @(posedge clk) disable iff (!clk) $fell(in) && $fell(clk) |-> (state != next_state)
  );
endmodule