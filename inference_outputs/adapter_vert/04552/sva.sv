property ClockSynceotid; @(posedge clk_in_13) (Y) |-> (or0_out == (B2 || B1)) && (or1_out == (A2 || A1)) && (nand0_out_Y == !(or1_out && or0_out && C1)) && (Y == nand0_out_Y); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_13) (Y) |-> (or0_out == (B2 || B1)) && (or1_out == (A2 || A1)) && (nand0_out_Y == !(or1_out && or0_out && C1)) && (Y == nand0_out_Y); endproperty 
 