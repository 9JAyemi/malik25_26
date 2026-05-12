property ClockSynceotid; @(posedge clk_osc_18) (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1) |-> X ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_18) (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1) |-> X ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_18) (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1) |-> X ;endproperty 
 