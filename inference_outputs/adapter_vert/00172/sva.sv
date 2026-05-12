property WakeUpeotid; @(posedge clk_osc_18) (X) |-> (SLEEP) != (SLEEP_B); endproperty 
 
 property WakeUpeotid; @(posedge clk_osc_18) (and0_out_X) |-> (SLEEP) && (A); endproperty 
 
 property WakeUpeotid; @(posedge clk_osc_18) (X) |-> (and0_out_X); endproperty 
 