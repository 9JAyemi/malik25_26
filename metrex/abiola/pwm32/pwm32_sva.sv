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
