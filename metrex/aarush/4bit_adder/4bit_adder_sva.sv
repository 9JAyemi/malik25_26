/*
 * SVA QUALITY EVALUATION
 * ======================
 * These assertions are combinational-only and misuse SVA syntax. Properties `p_adder_correct`
 * and `p_carry_correct` lack clock sampling - they're evaluated continuously as immediate
 * assertions but declared as properties, which is semantically incorrect for concurrent
 * verification. The fourth "assertion" in the always block is procedural code masquerading
 * as SVA, mixing blocking/non-blocking assignments with assertion logic, and won't catch
 * glitches properly since it relies on event triggers rather than sampled values. More
 * critically, there's no temporal checking whatsoever - for a combinational circuit, you
 * need stability assertions (output shouldn't change for epsilon time after inputs stabilize)
 * and propagation delay verification. The exhaustive stimulus is good, but assertions should
 * verify timing constraints like setup/hold would in real hardware. Coverage gaps: no check
 * for intermediate carry propagation correctness, no verification that all bits of sum
 * contribute correctly, and no metastability checks for near-simultaneous input changes.
 *
 * Most Significant Flaw: All properties are evaluated without clock context, making them
 * immediate assertions that check only current values, missing race conditions and glitches
 * that concurrent SVA with proper temporal operators would catch.
 *
 * Final Score: 4/10 - Functional correctness checks are present but fundamentally misapplied
 * SVA methodology for combinational logic undermines their verification value.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions fundamentally misuse SVA for a combinational circuit. The properties `p_adder_correct` and `p_carry_correct` are declared without a clocking event, making them simple immediate assertions that check for logical equivalence at all times. This approach is highly inefficient and prone to firing on transient glitches during combinational logic settling. The stability check within the `always @(a or b or cin)` block is a procedural assertion, not a concurrent one, and its use of a `#1` delay is a poor and non-synthesizable way to check for stability, which is also susceptible to race conditions.
 *
 * The verification is incomplete as it fails to check key aspects of an adder's physical behavior. There are no assertions to verify the propagation delay from input changes to output stability, which is a critical parameter. Furthermore, the assertions do not check the correctness of the internal carry chain (e.g., the carry-out of each full adder stage), which could mask implementation bugs. The `p_no_xz_outputs` check is useful but, like the others, is an immediate assertion that provides no temporal guarantees.
 *
 * Most Significant Flaw: The complete lack of proper, clock-sampled concurrent assertions makes the entire suite incapable of verifying temporal characteristics like stability and propagation delay, which are critical for combinational logic.
 *
 * Final Score: 2/10 - The assertions only perform basic logical checks and are implemented using an incorrect and inefficient methodology for SVA.
 */

`timescale 1ns/1ps

module tb_four_bit_adder;

  // DUT I/O
  logic [3:0] a, b;
  logic cin;
  logic [3:0] sum;
  logic cout;

  // DUT instantiation
  four_bit_adder dut (
    .a(a),
    .b(b),
    .cin(cin),
    .sum(sum),
    .cout(cout)
  );

  // ==============================================================
  // STIMULUS
  // ==============================================================

  initial begin
    // Test all possible combinations exhaustively
    for (int i = 0; i < 16; i++) begin
      for (int j = 0; j < 16; j++) begin
        for (int k = 0; k < 2; k++) begin
          a = i;
          b = j;
          cin = k;
          #1; // allow time for combinational settle
        end
      end
    end
    $display("All combinations tested.");
    $finish;
  end

  // ==============================================================
  // SYSTEMVERILOG ASSERTIONS
  // ==============================================================

  // 1. Functional correctness of sum and cout
  property p_adder_correct;
    ({cout, sum} == (a + b + cin));
  endproperty
  assert property (p_adder_correct)
    else $error("Adder output mismatch: a=%0d b=%0d cin=%0d -> sum=%0d cout=%0d",
                a, b, cin, sum, cout);

  // 2. Carry correctness
  property p_carry_correct;
    (cout == ((a + b + cin) > 4'b1111));
  endproperty
  assert property (p_carry_correct)
    else $error("Carry output incorrect for a=%0d b=%0d cin=%0d", a, b, cin);

  // 3. No unknown or high-impedance values on outputs
  property p_no_xz_outputs;
    !$isunknown({sum, cout});
  endproperty
  assert property (p_no_xz_outputs)
    else $error("Unknown (X/Z) detected on outputs!");

  // 4. Output stability (sum, cout do not change unless inputs change)
  logic [3:0] prev_sum;
  logic prev_cout;
  always @(a or b or cin) begin
    prev_sum = sum;
    prev_cout = cout;
    #1;
    if ((a === a) && (b === b) && (cin === cin)) begin
      assert (sum === (a + b + cin)[3:0])
        else $error("Output changed without input change!");
    end
  end

endmodule
