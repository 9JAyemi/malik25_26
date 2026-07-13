property ClockSynceotid; @(posedge clk_osc_15) (Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_15) (or0_out_Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_15) (or0_out_Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_osc_15) (or0_out_Y) |-> (or0_out_Y == 1'b1) && (nor0_out == 1'b0) && (nor1_out == 1'b0) ;endproperty 
 