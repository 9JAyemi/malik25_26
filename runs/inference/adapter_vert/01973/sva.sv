property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out) && (and0_out_X); endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (or0_out) &&  (  (A2) || (A1) || (A3)  ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (and0_out_X) |->  (  (or0_out)  && (  (B1)  )  ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (X) == (and0_out_X) ; endproperty 
 