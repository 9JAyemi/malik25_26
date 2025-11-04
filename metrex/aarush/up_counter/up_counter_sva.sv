/*
 * SVA QUALITY EVALUATION
 * ======================
 * The assertions contain critical correctness flaws. Property `increment_behavior` uses
 * `$past(dut.count_reg + 1)` which evaluates the addition BEFORE taking the past value,
 * making it equivalent to `$past(dut.count_reg) + 1`, but the syntax is misleading and
 * could fail synthesis. More critically, the reset check uses `&&` between two conditions
 * in the consequent without proper grouping - it checks if count_out equals 0, but doesn't
 * verify count_reg resets properly due to the assertion structure. The wrap-around property
 * has a race condition: it checks if the PAST value was 0xFFFF, but doesn't account for
 * when reset might occur at that exact moment. Coverage is incomplete - no assertions verify
 * the counter maintains correct behavior across the full 16-bit range, only the output
 * mapping is checked. Missing: stability checks when select changes mid-operation, and no
 * verification that count_reg increments monotonically without glitches.
 *
 * Most Significant Flaw: The `increment_behavior` property is fundamentally broken - it
 * compares count_reg against its own past incremented value, which will always fail because
 * it's checking if X == X+1, not if X == PAST(X)+1.
 *
 * Final Score: 3/10 - Multiple logical errors render key assertions non-functional, though
 * the select output mapping checks are structurally sound.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions contain severe correctness and completeness issues. The `increment_behavior` property is logically incorrect, as it checks `dut.count_reg == $past(dut.count_reg + 1)`, which compares a register's current value with the past value of an expression involving itself, rather than the correct `dut.count_reg == $past(dut.count_reg) + 1`. The `reset_clears` property is also flawed; its consequent `(dut.count_reg == 16'h0000 && dut.count_out == 4'h0)` should be `(dut.count_reg == 16'h0) && (dut.count_out == 4'h0)` to be syntactically correct and clear.
 *
 * The verification is critically incomplete. It fails to check for glitches or stability on `count_out` when `select` changes, a common source of bugs. There are no assertions to ensure the counter increments monotonically only when enabled and does not change otherwise. The `wrap_around_check` is insufficient as it only covers the transition from `FFFF` to `0000` but not other corner cases like `FFFE` to `FFFF`. The properties for `select` behavior only check the output mapping but not the timing or potential hazards.
 *
 * Most Significant Flaw: The `increment_behavior` property is fundamentally broken, failing to verify the primary function of the counter, which is to increment correctly.
 *
 * Final Score: 2/10 - The core functional assertion is incorrect, and the suite misses numerous critical checks for a simple counter, rendering it ineffective.
 */

`timescale 1ns / 1ps

module tb_up_counter;

  // DUT signals
  logic clk;
  logic reset;
  logic select;
  wire [3:0] count_out;

  // Instantiate DUT
  up_counter dut (
    .clk(clk),
    .reset(reset),
    .select(select),
    .count_out(count_out)
  );

  // Clock generation
  always #5 clk = ~clk;

  // Stimulus
  initial begin
    clk = 0;
    reset = 1;
    select = 0;
    #10;
    reset = 0;

    // Normal counting mode
    repeat (5) @(posedge clk);
    
    // Complement select mode
    select = 1;
    repeat (5) @(posedge clk);

    // Reset again
    reset = 1;
    @(posedge clk);
    reset = 0;

    repeat (5) @(posedge clk);

    $finish;
  end

  // -------------------------------
  // SYSTEMVERILOG ASSERTIONS (SVA)
  // -------------------------------

  // 1️⃣ Reset clears both registers
  property reset_clears;
    @(posedge clk) reset |-> (dut.count_reg == 16'h0000 && dut.count_out == 4'h0);
  endproperty
  assert property (reset_clears)
    else $error("❌ Reset did not clear count_reg and count_out");

  // 2️⃣ Count increments by 1 each cycle when not reset
  property increment_behavior;
    @(posedge clk) disable iff (reset)
      dut.count_reg == $past(dut.count_reg + 1);
  endproperty
  assert property (increment_behavior)
    else $error("❌ count_reg did not increment correctly");

  // 3️⃣ When select = 0, output should match lower 4 bits of count_reg
  property select_zero_behavior;
    @(posedge clk) disable iff (reset)
      (!select) |-> (count_out == dut.count_reg[3:0]);
  endproperty
  assert property (select_zero_behavior)
    else $error("❌ count_out mismatch when select=0");

  // 4️⃣ When select = 1, output should be bitwise complement of count_reg[3:0]
  property select_one_behavior;
    @(posedge clk) disable iff (reset)
      (select) |-> (count_out == ~dut.count_reg[3:0]);
  endproperty
  assert property (select_one_behavior)
    else $error("❌ count_out mismatch when select=1");

  // 5️⃣ Overflow wrap-around check (for count_reg)
  property wrap_around_check;
    @(posedge clk) disable iff (reset)
      ($past(dut.count_reg) == 16'hFFFF) |-> (dut.count_reg == 16'h0000);
  endproperty
  assert property (wrap_around_check)
    else $error("❌ Counter did not wrap around after 0xFFFF");

endmodule
