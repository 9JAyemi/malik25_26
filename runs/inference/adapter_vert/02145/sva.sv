property ClockSynceotid; @(posedge clk_in_1) (sel) == (0) |-> (out) == (a) ; endproperty 
 
 property SyncEqeotid; @(posedge clk_in_1) (sel) != 0 |-> (out) == (b) ; endproperty 
 