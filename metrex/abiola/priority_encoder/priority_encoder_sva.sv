/*
 * SVA QUALITY EVALUATION
 * ======================
 * The property `p_output_follows_input` has a critical temporal error: it uses `$rose(clk)` within
 * a `@(posedge clk)` context, which is redundant and always true at posedge, then checks if output
 * at cycle N+1 equals the expected code of input at cycle N+1, not N. The correct formulation should
 * be `|-> ##1 (O == expected_code($past(I)))` to verify the registered delay. The stability check
 * using negedge is procedural rather than proper SVA and creates sampling issues - combinational
 * glitches between clock edges won't be caught reliably. The one-hot input assertion is reasonable
 * but the `expected_code` function doesn't implement true priority encoding - it assumes one-hot
 * input only, but priority encoders should handle multi-hot inputs by selecting the highest priority
 * bit. If multiple bits are set, the function returns 2'b00 (default), which doesn't verify correct
 * priority behavior. Missing coverage: no verification of what happens when input violates one-hot
 * assumption during actual operation, no checks for output stability across input changes, and no
 * assertion that validates priority ordering (e.g., if I[3:2] are both set, I[3] should win).
 *
 * Most Significant Flaw: Property `p_output_follows_input` checks if output matches the CURRENT
 * input's expected code rather than the PREVIOUS cycle's input, failing to verify the registered
 * delay behavior that's central to the clocked encoder.
 *
 * Final Score: 4/10 - Structural approach is reasonable but temporal logic is incorrect for the
 * registered design, and priority encoding behavior is not actually verified.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions contain significant correctness and completeness issues. The main property, `p_output_follows_input`, is temporally incorrect; it checks if the output `O` at cycle N+1 matches the encoded input `I` from the same cycle (N+1), not the previous one (N). This fails to verify the one-cycle latency of the registered design. The stability check is a procedural assertion using `negedge clk`, which is not robust for catching glitches and is poor SVA practice.
 *
 * The verification is critically incomplete because it fails to test the "priority" aspect of the encoder. The helper function `expected_code` and the immediate assertion `is_onehot_or_zero` enforce a one-hot input constraint, effectively preventing any test of multi-hot inputs where priority logic is required. The default case in `expected_code` returns `2'b00`, meaning if a multi-hot input is ever provided, the assertion will check for a default output rather than the correctly prioritized one. The core function is thus left unverified.
 *
 * Most Significant Flaw: The assertions and helper functions are designed to only test one-hot inputs, completely failing to verify the priority logic that is central to a priority encoder's function.
 *
 * Final Score: 3/10 - The temporal logic is flawed, and the test strategy actively avoids verifying the DUT's primary "priority" feature.
 */

// SystemVerilog Assertions for priority_encoder.v
// Created: 2025-10-22

`timescale 1ns/1ps

module priority_encoder_sva();

  // Clock and DUT signals declared as interface-slice for formal checking
  logic clk;
  logic [3:0] I;
  logic [1:0] O;

  // Instantiate DUT (behavioral connection for SVA checks)
  // The DUT in the RTL is named priority_encoder and has clocked behavior
  priority_encoder dut (
    .I(I),
    .clk(clk),
    .O(O)
  );

  // Simple clock generator for simulation-based assertion checking
  initial clk = 0;
  always #5 clk = ~clk; // 100MHz-like for checks

  // ==================================================================
  // Helper predicates
  // ==================================================================

  // Input one-hot or zero (allow zero vector). Exactly one or zero bits set.
  function automatic bit is_onehot_or_zero(logic [3:0] v);
    int unsigned cnt;
    cnt = $countones(v);
    return (cnt == 1) || (cnt == 0);
  endfunction

  // Map I to expected 2-bit code. If zero -> 2'b00 (as in RTL default)
  function automatic logic [1:0] expected_code(logic [3:0] v);
    case (v)
      4'b0001: expected_code = 2'b00;
      4'b0010: expected_code = 2'b01;
      4'b0100: expected_code = 2'b10;
      4'b1000: expected_code = 2'b11;
      default: expected_code = 2'b00;
    endcase
  endfunction

  // ==================================================================
  // Interface checks
  // ==================================================================

  // Check: input is always one-hot or zero (design may accept else but assert
  // can flag unexpected multi-hot inputs). Use immediate assert in clock domain.
  always @(posedge clk) begin
    // If this fires, the testbench is driving illegal multi-hot input
    assert (is_onehot_or_zero(I)) else $error("I is not one-hot or zero: %b", I);
  end

  // ==================================================================
  // Functional properties
  // ==================================================================

  // Property 1: The registered output O must always equal expected_code of the
  // stage1_out from previous combinational mapping (i.e., one-cycle delayed).
  // We encode: if I at cycle N is code C, then O at cycle N+1 must be C.
  property p_output_follows_input;
    @(posedge clk) disable iff (0) $rose(clk) |-> ##1 (O == expected_code(I));
  endproperty
  // Bind and assert
  assert property (p_output_follows_input) else $error("O did not follow expected code from I on next cycle: I=%b O=%b", I, O);

  // Property 2: O must be stable within the clock cycle except at the register update
  // (i.e., no mid-cycle changes). We sample O on posedge and negedge to check stability.
  logic [1:0] O_posedge;
  always @(posedge clk) O_posedge <= O;
  always @(negedge clk) begin
    assert (O == O_posedge) else $error("O changed in the clock half-cycle: posedge O=%b negedge O=%b", O_posedge, O);
  end

  // Property 3: If I is zero, O should be 2'b00 after the clock edge (default behavior)
  property p_zero_input_sets_zero_output;
    @(posedge clk) disable iff (0) (I == 4'b0000) |-> ##1 (O == 2'b00);
  endproperty
  assert property (p_zero_input_sets_zero_output) else $error("Zero input did not produce O==00 next cycle when expected: I=%b O=%b", I, O);

  // Cover some scenarios for simulation-based coverage
  initial begin
    // randomize inputs a few times to exercise assertions in simulation
    I = 4'b0000; #20;
    I = 4'b0001; #20;
    I = 4'b0010; #20;
    I = 4'b0100; #20;
    I = 4'b1000; #20;
    // multi-hot input to show assertion trigger (optional)
    I = 4'b0011; #20;
    $finish;
  end

endmodule
