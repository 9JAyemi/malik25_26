property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (and0_out) && !(nor0_out_Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) &&  (  !(and0_out)  &&  (nor0_out_Y)  ) |-> (Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) &&  (  (and0_out)  &&  !(nor0_out_Y)  ) |-> (Y) ;endproperty 
 