property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (b) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) |-> (and0_out) && (A1) && (A2) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_19) (nor0_out_Y) |-> ! (b) || ! (and0_out) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (nor0_out_Y) ;endproperty 
 