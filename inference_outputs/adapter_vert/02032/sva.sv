property ClockSynceotid; @(posedge clk_osc_19) (or0_out) |-> (nand0_out_Y); endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (or0_out) &&  (  (B1) &&  (or0_out)  ) |-> (nand0_out_Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (or0_out) &&  (  (B1) &&  !(or0_out)  ) |-> !(nand0_out_Y) ; endproperty 
 