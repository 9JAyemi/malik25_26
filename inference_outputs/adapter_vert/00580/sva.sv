property SubSynceotid; @(posedge clk_in_12) (B) |-> (B_comp) ;endproperty 
 
 property SyncSubeotid; @(posedge clk_in_12) (A) != (B) |-> (S) == (A + B_comp) ;endproperty 
 
 property SyncSubeotid; @(posedge clk_in_12) (B) |-> (S) == (A + B_comp) ;endproperty 
 