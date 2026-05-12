property MaxSynceotid; @(posedge clk_in_1) (a) > (b) |-> (max) == (a) ; endproperty 
 
 property SyncEqeotid; @(posedge clk_in_1) (c) > (d) |-> (max) == (c) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (a) <= (b) && (c) <= (d) |-> (max) == (d) ; endproperty 
 