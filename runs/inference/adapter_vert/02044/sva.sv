property ClockSynceotid; @(posedge clk_osc_19) (X) |-> (and1_out) && (and0_out) && (or0_out_X); endproperty 
 
 property SyncCheckeotid; @(posedge clk_osc_19) (and1_out) && (and0_out) == (1'b1) |-> (or0_out_X) ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_19) (and1_out) && (and0_out) && (or0_out_X) |-> (X) ; endproperty 
 