// SVA for PWM32
checker pwm32_chk;
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Sanity: definition equivalences
  assert property (timer_clk == (clkdiv == PRE));
  assert property (tmrov     == (TMR    == TMRCMP1));
  assert property (pwmov     == (TMR    == TMRCMP2));

  // Prescaler (clkdiv) behavior
  assert property (timer_clk |=> clkdiv == 32'd0);
  assert property (TMREN && !timer_clk |=> clkdiv == $past(clkdiv) + 32'd1);
  assert property (!TMREN && !timer_clk |=> clkdiv == $past(clkdiv));
  // Changes only due to TMREN increment or timer_clk reset
  assert property ($changed(clkdiv) |-> $past(timer_clk) || $past(TMREN) || $past(rst));

  // Timer (TMR) behavior and priority
  assert property (tmrov |=> TMR == 32'd0);                         // reset has priority
  assert property (!tmrov && timer_clk |=> TMR == $past(TMR) + 32'd1);
  assert property (!tmrov && !timer_clk |=> TMR == $past(TMR));
  assert property ($changed(TMR) |-> $past(timer_clk) || $past(tmrov) || $past(rst));

  // PWM output behavior and priority
  assert property (pwmov |=> pwm == 1'b1);
  assert property (!pwmov && tmrov |=> pwm == 1'b0);
  assert property (pwmov && tmrov |=> pwm == 1'b1);                 // pwmov has priority
  assert property (pwm && !tmrov |=> pwm);                          // holds high until tmrov
  // Edge-justification (cause of transitions)
  assert property ($rose(pwm) |-> $past(pwmov));
  assert property ($fell(pwm) |-> $past(tmrov) && !$past(pwmov));

  // Asynchronous reset effects observed on next clk edge
  assert property (@(posedge clk) disable iff (1'b0)
                   rst |=> (clkdiv == 32'd0 && TMR == 32'd0 && pwm == 1'b0));

  // Coverage
  cover property (TMREN ##[1:$] timer_clk);                         // prescaler tick while enabled
  cover property (tmrov ##[1:$] pwmov ##[1:$] tmrov);               // a full PWM cycle
  cover property (pwmov && tmrov);                                  // equal compares priority case
  cover property (PRE == 32'd0 ##1 timer_clk);                      // zero-prescale behavior
  cover property (!TMREN [*2] ##1 TMREN ##[1:20] timer_clk);        // enable gating then tick
endchecker

bind PWM32 pwm32_chk pwm32_chk_i();