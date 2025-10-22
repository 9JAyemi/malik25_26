analyze -sv pwm32.v

elaborate -top PWM32

clock clk
reset rst

# Reset properties: registers zeroed on reset
assert { rst |-> (TMR == 32'd0 && clkdiv == 32'd0 && pwm == 1'b0) }

# Prescaler behavior: when clkdiv equals PRE, timer_clk asserted next cycle
assert { clkdiv == PRE |-> ##1 timer_clk }

# When TMREN is high and not timer_clk, clkdiv increments by 1 on next cycle
assume { TMREN }
assert { (!timer_clk && TMREN && !rst) |-> ##1 (clkdiv == $past(clkdiv) + 32'd1) }

# Timer increment: if timer_clk and not tmrov, TMR increments by 1 next cycle
assert { timer_clk && !tmrov && !rst |-> ##1 (TMR == $past(TMR) + 32'd1) }

# Timer wrap: when TMR equals TMRCMP1 then tmrov true and next cycle TMR == 0
assert { TMR == TMRCMP1 |-> ##1 (TMR == 32'd0) }

# PWM behavior: pwm set to 1 when TMR == TMRCMP2, reset to 0 when tmrov
assert { TMR == TMRCMP2 |-> ##1 (pwm == 1'b1) }
assert { tmrov |-> ##1 (pwm == 1'b0) }

# Prover options
set_prove_time_limit 3600
set_engine_mode Tri
prove -all
