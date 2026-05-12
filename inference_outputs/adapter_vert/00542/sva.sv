property ClockSynceotid; @(posedge clk_osc_14) (and0_out) == (A3 & A1 & A2) ; endproperty 
 
 property SyncOkeotid; @(posedge clk_osc_14) (or0_out_X) == (and0_out | B1) ; endproperty 
 
 property PowerSynceotid; @(posedge clk_osc_14) (X) == (or0_out_X) ; endproperty 
 