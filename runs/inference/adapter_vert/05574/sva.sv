property ClockSynceotid; @(posedge clk_osc_19) (Y) |-> (nand0_out) && (or0_out) && (nand1_out_Y); endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (Y) == (nand1_out_Y) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (Y) |-> (nand0_out) && (or0_out) && (nand1_out_Y); endproperty 
 