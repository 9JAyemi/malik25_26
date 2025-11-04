/*
 * SVA QUALITY EVALUATION
 * ======================
 * The state machine assertions are structurally flawed and incomplete. Property `p_state_transition`
 * uses chained `|=>` operators incorrectly - the sequence `(state==00) |=> (state==01) ##1 (state==01) |=>...`
 * doesn't create a continuous chain but rather separate implications that never trigger together.
 * Property `p_valid_transitions` uses `or` to connect multiple implications, which always evaluates
 * true as long as ANY transition is valid, not checking if the ACTUAL transition matches expectations.
 * The critical flaw: `state_in` input is never used or verified - the FSM appears to have an input
 * signal that might affect transitions, but no assertions check its behavior. Property `p_output_correctness`
 * lumps states 00 and 11 together with identical outputs, but doesn't verify WHY state 11 exists or
 * what triggers it versus 00. Missing coverage: no timing requirements for state duration (traffic
 * lights should stay in each state for minimum time), no verification of transition conditions beyond
 * sequence, and no liveness properties ensuring the FSM doesn't deadlock in a state.
 *
 * Most Significant Flaw: The transition checking logic is fundamentally broken - using `or` between
 * separate implications means the assertion passes even when invalid transitions occur, as long as
 * at least one valid transition type exists somewhere in the trace.
 *
 * Final Score: 4/10 - Reset and mutual exclusion checks work, but core FSM transition verification
 * is logically incorrect and would miss most state machine bugs.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions for state transitions are logically flawed and ineffective. The property `p_valid_transitions` uses an `or` chain of implications, which is a critical error; this property will pass as long as the machine is in any valid state, as one of the clauses will be true, but it fails to enforce that the *correct* next state is reached. For example, if the state is `2'b00`, the assertion does not fail if the next state is `2'b10` instead of the expected `2'b01`. The `p_state_transition` property is also syntactically confused and would not enforce a sequential path.
 *
 * The verification is critically incomplete because it completely ignores the `state_in` input. The DUT has an input that presumably controls its behavior (e.g., forcing a state change), but no assertions verify its effect on the state transitions. This leaves a significant part of the DUT's logic untested. Furthermore, there are no liveness properties to ensure the FSM does not get stuck, nor are there any checks on the duration of each state, which is a key requirement for a real-world traffic light.
 *
 * Most Significant Flaw: The `p_valid_transitions` property is logically incorrect, as its use of `or` prevents it from actually constraining state transitions, allowing illegal state changes to pass verification.
 *
 * Final Score: 2/10 - The core FSM transition logic is not correctly verified, and a key input is completely ignored, making the assertion suite fundamentally unreliable.
 */

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
