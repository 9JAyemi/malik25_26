property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (or0_out_X); endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and1_out) &&  ( (A1) &&  (A2) ) |->  (and0_out) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and2_out) &&  ( (C1) &&  (C2) ) |->  (and0_out) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (or0_out_X) |->  (and1_out) &&  (and0_out) &&  (and2_out) ; endproperty 
 