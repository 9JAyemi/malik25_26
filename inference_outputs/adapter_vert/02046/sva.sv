property ClockSynceotid; @(posedge clk_osc_19) (A_N) |-> not0_out ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (B) && @(posedge clk_osc_19) (C) && @(posedge clk_osc_19) (D) |-> and0_out_X ;endproperty 
 
 property PowerSynceotid; @(posedge clk_osc_19) (and0_out_X) && @(posedge clk_osc_19) (VPWR) && @(posedge clk_osc_19) (VGND) |-> pwrgood_pp0_out_X ;endproperty 
 
 property ValidOuteotid; @(posedge clk_osc_19) (pwrgood_pp0_out_X) |-> X ;endproperty 
 