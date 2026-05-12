property WakeUpeotid; @(posedge clk_osc_17) (X) |-> (SLEEP) != (A); endproperty 
 
 property WakeUpeotid; @(posedge clk_osc_17) (X) |-> (and0_out_X) && (SLEEP_B); endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_17) (X) == (and0_out_X) &&  ( (SLEEP) != (A) ); endproperty 
 