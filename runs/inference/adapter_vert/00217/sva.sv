property ClockSynceotid; @(posedge clk_in_18) (Y) |-> (or0_out == 1'b1) && (or1_out == 1'b1) && (nand0_out_Y == 1'b0); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_18) (or0_out) |-> (B2 == 1'b1) && (B1 == 1'b1); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_18) (or1_out) |-> (A2 == 1'b1) && (A1 == 1'b1); endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_18) (nand0_out_Y) |-> (or1_out == 1'b1) && (or0_out == 1'b1) && (C1 == 1'b0); endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_18) (Y) |-> (nand0_out_Y == 1'b0); endproperty 
 