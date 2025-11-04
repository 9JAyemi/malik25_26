/*
 * SVA QUALITY EVALUATION
 * ======================
 * These assertions are entirely procedural and do not utilize proper SVA syntax or methodology.
 * All checks are implemented as immediate assertions within always blocks, missing the power of
 * concurrent assertions with temporal operators. The shift-register checks have a critical timing
 * flaw: they use `$past()` which samples at the previous clock edge, but the comparisons happen
 * within the same always block, creating race conditions where register updates and assertion
 * evaluation occur simultaneously. The FSM progression checks are logically broken - the condition
 * `$past(dut.state) != 3'b001 || dut.state == 3'b010` uses OR incorrectly, making it always pass
 * when state equals 010 regardless of previous state. More critically, there's no verification of
 * the edge detection correctness itself - when input changes, does output correctly reflect the
 * detected edge? The assertions only check internal FSM state transitions but never validate the
 * module's actual function (detecting edges). Missing coverage: no checks for output stability,
 * metastability on input changes, or verification that edges are detected within expected latency.
 *
 * Most Significant Flaw: All assertions are immediate procedural checks rather than proper SVA
 * properties, eliminating temporal verification capabilities and creating race conditions between
 * register updates and assertion evaluation.
 *
 * Final Score: 3/10 - Fundamentally misunderstands SVA methodology by using only immediate assertions,
 * and the FSM transition logic contains errors that would allow invalid behavior to pass.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * This set of assertions remains fundamentally flawed by exclusively using immediate assertions within `always` blocks, which is not the intended use for concurrent, temporal verification. The FSM progression check `($past(dut.state) != 3'b001 || dut.state == 3'b010)` is logically incorrect; the `||` operator allows the assertion to pass if `dut.state` is `3'b010`, regardless of the previous state, thus failing to enforce a strict transition. The shift-register checks, such as `assert (dut.prev_in == $past(dut.curr_in))`, create a race condition by comparing a signal to its past value within the same clocking event where it is updated, leading to unpredictable results.
 *
 * The verification is critically incomplete as it fails to check the module's primary output `out`. The assertions only inspect internal state machine and register behavior but never confirm that a detected edge produces the correct output signal. Key properties like the latency from input change to output assertion, the duration of the output pulse, and the absence of output glitches are entirely missing. The entire functional purpose of the edge detector—its output—is left unverified.
 *
 * Most Significant Flaw: The complete failure to verify the module's output (`out`), meaning the assertions could all pass while the DUT produces entirely incorrect results.
 *
 * Final Score: 2/10 - The assertions are logically unsound, implemented with poor methodology, and fail to verify the core functionality of the DUT.
 */

`timescale 1ns/1ps

module edge_detector_sva();

  logic clk;
  logic [7:0] in;
  logic [7:0] out;

  edge_detector dut (
    .clk(clk),
    .in(in),
    .out(out)
  );

  // clock
  initial clk = 0;
  always #5 clk = ~clk;

  // When input changes (curr_in != prev_in), FSM should transition to state 3'b001
  always @(posedge clk) begin
    if (dut.curr_in != dut.prev_in)
      assert (dut.state == 3'b001) else $error("Change not detected: prev=%b curr=%b state=%b", dut.prev_in, dut.curr_in, dut.state);
  end

  // Check FSM progression
  always @(posedge clk) begin
    if (dut.state == 3'b001)
      assert ($past(dut.state) != 3'b001 || dut.state == 3'b010) else $error("State did not progress 001->010");
    if (dut.state == 3'b010)
      assert ($past(dut.state) != 3'b010 || dut.state == 3'b011) else $error("State did not progress 010->011");
    if (dut.state == 3'b011)
      assert (out == dut.next_in) else $error("out != next_in when in state 011: out=%b next_in=%b", out, dut.next_in);
  end

  // Shift-register behavior across posedges
  always @(posedge clk) begin
    assert (dut.prev_in == $past(dut.curr_in)) else $error("prev_in didn't capture curr_in");
    assert (dut.curr_in == $past(dut.next_in)) else $error("curr_in didn't capture next_in");
    assert (dut.next_in == $past(in)) else $error("next_in didn't capture in");
  end

  // small stimulus for simulation
  initial begin
    in = 8'h00; #20;
    in = 8'hFF; #100;
    in = 8'h0F; #100;
    $finish;
  end

endmodule
