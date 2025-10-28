`timescale 1ns/1ps

module tb_traffic_light_controller;

  // DUT I/O
  logic clk;
  logic reset;
  logic [1:0] state_in;
  logic [1:0] state_out;
  logic red, green;

  // Instantiate DUT
  traffic_light_controller dut (
    .clk(clk),
    .reset(reset),
    .state_in(state_in),
    .state_out(state_out),
    .red(red),
    .green(green)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Stimulus
  initial begin
    clk = 0;
    reset = 1;
    state_in = 2'b00;
    #10;
    reset = 0;

    // Let it run through several state cycles
    repeat (10) @(posedge clk);
    $finish;
  end

  // ==============================================================
  // SYSTEMVERILOG ASSERTIONS
  // ==============================================================

  // 1. Reset behavior: after reset, state_out must be 000, red=1, green=0
  property p_reset_behavior;
    @(posedge clk) reset |-> (state_out == 2'b00 && red && !green);
  endproperty
  assert property(p_reset_behavior)
    else $error("Reset behavior violated!");

  // 2. State transition sequence: 000 -> 001 -> 010 -> 011 -> 000
  property p_state_transition;
    @(posedge clk) disable iff (reset)
      (state_out == 2'b00) |=> (state_out == 2'b01) ##1
      (state_out == 2'b01) |=> (state_out == 2'b10) ##1
      (state_out == 2'b10) |=> (state_out == 2'b00 || state_out == 2'b11);
  endproperty

  // (Simpler: check one step at a time)
  property p_valid_transitions;
    @(posedge clk) disable iff (reset)
      ((state_out == 2'b00) |-> ##1 (state_out == 2'b01)) or
      ((state_out == 2'b01) |-> ##1 (state_out == 2'b10)) or
      ((state_out == 2'b10) |-> ##1 (state_out == 2'b00 || state_out == 2'b11)) or
      ((state_out == 2'b11) |-> ##1 (state_out == 2'b00));
  endproperty
  assert property(p_valid_transitions)
    else $error("Invalid state transition detected!");

  // 3. Output correctness based on state_out
  property p_output_correctness;
    @(posedge clk)
      ((state_out == 2'b00 || state_out == 2'b11) |-> (red && !green)) and
      ((state_out == 2'b01) |-> (!red && green)) and
      ((state_out == 2'b10) |-> (red && !green));
  endproperty
  assert property(p_output_correctness)
    else $error("Output mismatch with state!");

  // 4. No illegal states (since only 000–011 are valid)
  property p_legal_state;
    @(posedge clk) disable iff (reset)
      (state_out inside {2'b00, 2'b01, 2'b10, 2'b11});
  endproperty
  assert property(p_legal_state)
    else $error("Illegal state detected!");

  // 5. Check that red and green are never both ON
  property p_mutual_exclusion;
    @(posedge clk) disable iff (reset)
      !(red && green);
  endproperty
  assert property(p_mutual_exclusion)
    else $error("Both red and green lights are ON simultaneously!");

endmodule
