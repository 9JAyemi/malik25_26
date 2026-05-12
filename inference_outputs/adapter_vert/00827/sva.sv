property SyncEqeotid; @(posedge clk_in_1) (a) == (b) |-> (out) == (a) ; endproperty 
 
 property SyncGoeotid; @(posedge clk_in_1) (a) != (b) && (a) >= (b) |-> (out) == (a) ; endproperty 
 
 property SyncGoeotid; @(posedge clk_in_1) (a) != (b) && (b) > (a) |-> (out) == (b) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (a) != (b) && (a) < (b)  |-> (out) == 7'b0000000 ; endproperty 
 