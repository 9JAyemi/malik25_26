property ClockSynceotid; @(posedge clk_osc_13) (X) |-> (or0_out) && (and0_out_X); endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_13) (or0_out) &&  (  (A2) || (A1)  ) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_13) (and0_out_X) |->  (  (or0_out) && (B1) && (C1)  ) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_13) (X) == (and0_out_X) ; endproperty 
 