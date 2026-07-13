property ResetSynceotid; @(posedge clk) (rst_n) |-> pwm_out == 1'b0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (rst_n) |-> pwm_out != pwm_out ;endproperty 
 