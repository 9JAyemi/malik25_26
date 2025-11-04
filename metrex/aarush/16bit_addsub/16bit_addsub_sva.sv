/*
 * SVA QUALITY EVALUATION
 * ======================
 * The overflow detection property contains a critical logic error: it computes `b_effective`
 * as `(~b + 1'b1)` for subtraction, but then adds `dut.carry` in the expected_sum calculation,
 * causing double-negation issues when carry is involved. The overflow formula checks if operand
 * signs match and result sign differs, which is correct for addition but fails for subtraction
 * since b_effective changes the sign relationship. Property `p_arithmetic_correct` references
 * `dut.carry` without verification that carry itself is correctly maintained - if carry is
 * corrupted, the assertion will pass incorrect results. The glitch detection in the procedural
 * block using `($time % 10 == 0)` is fragile and assumes perfect 10ns clock period with no
 * jitter; it also fires on initialization when $time=0. Missing coverage: no verification of
 * carry propagation between operations, no check that subtraction actually uses two's complement
 * correctly, and no assertions for intermediate `temp` register state or pipeline behavior if
 * multi-cycle operation is intended.
 *
 * Most Significant Flaw: The overflow property's logic is mathematically incorrect for
 * subtraction - it doesn't properly account for sign inversion of the subtrahend, causing
 * false passes on actual overflow conditions.
 *
 * Final Score: 5/10 - Core arithmetic checking exists but overflow verification and carry
 * handling have fundamental correctness issues that would miss real bugs.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions contain significant logical errors and are incomplete. The `p_overflow_correct` property is fundamentally flawed for subtraction; it calculates `b_effective` using two's complement but then compares `a[15]` with `b_effective[15]`, which does not correctly model the conditions for signed overflow in subtraction. The `p_arithmetic_correct` property depends on an unverified internal signal, `dut.carry`, making the check unreliable. The procedural glitch check is fragile, non-synthesizable, and relies on a hardcoded clock period.
 *
 * The verification coverage is poor. There are no assertions to verify the behavior of the internal `carry` signal itself, which is critical for both the arithmetic and overflow logic. The suite also fails to check specific corner cases that are essential for an adder/subtractor, such as adding/subtracting the maximum and minimum signed/unsigned values, operations resulting in zero, and toggling the `sub` signal while inputs `a` and `b` are stable. The correctness of the two's complement operation for subtraction is assumed rather than verified.
 *
 * Most Significant Flaw: The `p_overflow_correct` property uses an incorrect logical formula for detecting overflow during subtraction, meaning it will fail to catch actual overflow bugs.
 *
 * Final Score: 3/10 - The core arithmetic check is structurally present but relies on an unverified signal, and the critical overflow detection is logically incorrect.
 */

`timescale 1ns/1ps

module tb_addsub_16bit;

  // DUT signals
  logic clk;
  logic reset;
  logic [15:0] a, b;
  logic sub;
  logic [15:0] result;
  logic overflow;

  // Instantiate DUT
  addsub_16bit dut (
    .clk(clk),
    .reset(reset),
    .a(a),
    .b(b),
    .sub(sub),
    .result(result),
    .overflow(overflow)
  );

  // ==============================================================
  // Clock Generation
  // ==============================================================
  always #5 clk = ~clk;

  // ==============================================================
  // Stimulus
  // ==============================================================
  initial begin
    clk = 0;
    reset = 1;
    a = 0;
    b = 0;
    sub = 0;
    #10;
    reset = 0;

    // Run a mix of add/sub operations
    repeat (10) begin
      @(posedge clk);
      a = $random;
      b = $random;
      sub = $urandom_range(0, 1);
    end

    #20;
    $finish;
  end

  // ==============================================================
  // SYSTEMVERILOG ASSERTIONS
  // ==============================================================

  // 1. Reset behavior: temp and carry (implied through result) must reset
  property p_reset_behavior;
    @(posedge clk) reset |-> (result == 16'b0 && overflow == 0);
  endproperty
  assert property (p_reset_behavior)
    else $error("Reset failed to clear outputs");

  // 2. Correct arithmetic for ADD and SUB
  // We compute the expected result using SystemVerilog logic
  logic signed [16:0] expected_sum;
  always_comb begin
    if (sub)
      expected_sum = $signed(a) - $signed(b) + dut.carry;
    else
      expected_sum = $signed(a) + $signed(b) + dut.carry;
  end

  property p_arithmetic_correct;
    @(posedge clk) disable iff (reset)
      result == expected_sum[15:0];
  endproperty
  assert property (p_arithmetic_correct)
    else $error("Arithmetic result mismatch: a=%0d b=%0d sub=%b", a, b, sub);

  // 3. Overflow correctness
  logic signed [15:0] b_effective;
  always_comb begin
    b_effective = (sub) ? (~b + 1'b1) : b;
  end

  property p_overflow_correct;
    @(posedge clk) disable iff (reset)
      overflow == ((a[15] == b_effective[15]) && (result[15] != a[15]));
  endproperty
  assert property (p_overflow_correct)
    else $error("Overflow signal incorrect: a=%0h b=%0h result=%0h sub=%b",
                a, b, result, sub);

  // 4. No X/Z values on outputs
  property p_no_xz_outputs;
    @(posedge clk) !$isunknown({result, overflow});
  endproperty
  assert property (p_no_xz_outputs)
    else $error("Unknown (X/Z) value detected on outputs!");

  // 5. Outputs change only on clock edges
  // Capture result before clock and check for mid-cycle glitches
  logic [15:0] prev_result;
  logic prev_overflow;
  always @(posedge clk) begin
    prev_result <= result;
    prev_overflow <= overflow;
  end
  always @(result or overflow) begin
    if ($time > 0 && !$isunknown(result))
      assert ($time % 10 == 0)
        else $error("Glitch detected on result/overflow outside clock edge");
  end

endmodule
