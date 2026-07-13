property ClockSynceotid; @(posedge clk_osc_18) (Y) |-> (or0_out) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_18) (or0_out) &&  (  (B1) &&  (or0_out) &&  (nand0_out)  ) |-> (nand0_out) ;endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_18) (nand0_out) &&  (  (B1) &&  (or0_out) &&  (nand0_out)  ) |-> (Y) ;endproperty 
 