property ClockSynceotid; @(posedge clk_osc_18) (B1_N) |->  (b) ;endproperty 
 
 property SyncOkeotid; @(posedge clk_osc_18) (A2) ||  (A1) |->  (or0_out) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_18) (B1_N) &&  (A2) &&  (A1) |->  (nand0_out_Y) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_18) (B1_N) &&  (A2) &&  (A1) |->  (Y) ;endproperty 
 