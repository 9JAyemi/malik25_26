/*
 * SVA QUALITY EVALUATION
 * ======================
 * All assertions are immediate procedural checks lacking proper SVA properties with temporal operators.
 * The timer increment assertion has a logic error: it checks `TMR == $past(TMR) + 1` but doesn't account
 * for the fact that TMR updates at the current clock edge while $past samples the previous value, creating
 * a timing mismatch where the check may pass or fail unpredictably depending on evaluation order. The PWM
 * behavior checks verify pwmov and tmrov flag effects but don't validate the actual PWM waveform correctness
 * - there's no assertion that PWM duty cycle matches (TMRCMP2-TMRCMP1)/period or that pulse width timing
 * is accurate. Critical missing coverage: no verification of clkdiv increment behavior (only checks when
 * it equals PRE), no validation that clkdiv resets after reaching PRE, no check for edge cases like
 * TMRCMP1 > TMRCMP2 or CMP values exceeding timer range, and no verification that TMREN actually gates
 * timer operation correctly in all states. The reset check doesn't verify that clkdiv resets, only TMR
 * and pwm. No assertions for metastability or setup/hold on configuration signal changes.
 *
 * Most Significant Flaw: Complete absence of PWM waveform correctness verification - assertions check
 * internal state machine behavior but never validate the actual output pulse timing, duty cycle, or
 * frequency against the configured compare values.
 *
 * Final Score: 4/10 - Basic state machine checks exist but fundamental PWM functionality (output waveform
 * correctness) is completely unverified, and all checks use procedural rather than proper SVA methodology.
 */

/*
 * SECOND SVA QUALITY EVALUATION
 * =============================
 * The assertions are implemented as immediate assertions within `always` blocks, a poor practice that fails to leverage SVA's temporal capabilities. The timer increment check, `assert (dut.TMR == $past(dut.TMR) + 32'd1)`, is prone to race conditions as it compares a value updated on the current clock edge with a value sampled on the previous edge within the same procedural block. The PWM behavior checks are superficial; they only confirm that `pwm` is set or cleared when internal flags (`pwmov`, `tmrov`) are asserted but do not verify the timing or correctness of the PWM output itself.
 *
 * This verification suite is critically incomplete. It completely fails to assert the primary function of a PWM module: generating a correct waveform. There are no assertions to check if the PWM period matches the `PRE` setting, if the duty cycle corresponds to `TMRCMP1` and `TMRCMP2`, or if the output `pwm` signal is stable between timer events. Furthermore, the prescaler logic (`clkdiv`) is only checked at its terminal count, with no verification that it increments correctly or resets upon reaching `PRE`.
 *
 * Most Significant Flaw: The complete absence of any assertion verifying the actual PWM output waveform's period, duty cycle, or timing against the input configuration registers.
 *
 * Final Score: 2/10 - The assertions are procedurally weak and fail to verify the core functionality of the PWM module, rendering them largely ineffective.
 */

`timescale 1ns/1ps

module pwm32_sva();

  logic clk;
  logic rst;
  logic [31:0] PRE;
  logic [31:0] TMRCMP1;
  logic [31:0] TMRCMP2;
  logic TMREN;
  logic pwm;

  PWM32 dut (
    .clk(clk),
    .rst(rst),
    .PRE(PRE),
    .TMRCMP1(TMRCMP1),
    .TMRCMP2(TMRCMP2),
    .TMREN(TMREN),
    .pwm(pwm)
  );

  // clock
  initial clk = 0;
  always #5 clk = ~clk;

  // Reset property: registers zeroed when rst asserted
  always @(posedge clk) begin
    if (rst)
      assert (dut.TMR == 32'd0 && dut.clkdiv == 32'd0 && pwm == 1'b0) else $error("Reset did not zero regs");
  end

  // Prescaler: when clkdiv == PRE then timer_clk becomes true (wire inside DUT)
  always @(posedge clk) begin
    if (!rst && dut.clkdiv == PRE)
      assert (dut.timer_clk) else $error("timer_clk not asserted when clkdiv==PRE");
  end

  // Timer increment behavior: on timer_clk and not tmrov, TMR increments
  always @(posedge clk) begin
    if (!rst && dut.timer_clk && !dut.tmrov && TMREN)
      assert (dut.TMR == $past(dut.TMR) + 32'd1) else $error("TMR didn't increment on timer_clk");
  end

  // Timer wrap on tmrov
  always @(posedge clk) begin
    if (!rst && dut.tmrov)
      assert (dut.TMR == 32'd0) else $error("TMR did not wrap to 0 on tmrov");
  end

  // PWM behavior
  always @(posedge clk) begin
    if (!rst && dut.pwmov)
      assert (pwm == 1'b1) else $error("pwm not set when pwmov asserted");
    if (!rst && dut.tmrov)
      assert (pwm == 1'b0) else $error("pwm not cleared when tmrov asserted");
  end

  // Simple stimulus for simulation-driven checks
  initial begin
    rst = 1; PRE = 32'd5; TMRCMP1 = 32'd10; TMRCMP2 = 32'd7; TMREN = 1; #20;
    rst = 0; #20;
    #500;
    $finish;
  end

endmodule
