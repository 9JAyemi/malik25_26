property ClockSynceotid; @(posedge clk_osc_14) (Y) |-> (or0_out) && !(nand0_out_Y) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_14) (or0_out) &&  (nand0_out_Y) |-> (Y) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_14) (or0_out) &&  !(nand0_out_Y)  |-> !(Y) ;endproperty 
 