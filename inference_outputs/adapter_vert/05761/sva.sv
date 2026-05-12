property SyncEqeotid; @(posedge clk_in_15) (S) |-> (MO) == (B) ; endproperty 
 
 property SyncEqeotid; @(posedge clk_in_15) (S) != 1 |-> (MO) == (A) ; endproperty 
 