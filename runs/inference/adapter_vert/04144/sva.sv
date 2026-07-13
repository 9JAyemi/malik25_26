property ClockSynceotid; @(posedge clk_in_1) (sel) |-> (out) == (b) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (a) ; endproperty 
 