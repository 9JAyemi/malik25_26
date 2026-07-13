property ClockSynceotid; @(posedge clk_in_11) (A) and (B) |-> and0_out ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_11) (C) and (D) |-> or0_out ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_11) (E) and (F) |-> and1_out ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_11) (G) and (H) |-> or1_out ; endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_11) (and0_out || or0_out || !and1_out || !or1_out) == (X) ; endproperty 
 