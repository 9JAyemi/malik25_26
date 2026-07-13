property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (and0_out) && !(nor0_out_Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and0_out) &&  (  !(B1)  &&  (A1)  &&  (A2)  ) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (nor0_out_Y) |->  (  !(B1)  &&  (A1)  &&  (A2)  ) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (Y) |->  (  !(B1)  &&  (A1)  &&  (A2)  ) ;endproperty 
 