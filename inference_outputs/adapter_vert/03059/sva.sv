property ResetSynceotid; @(posedge clk) (reset) |-> (q == 0) ;endproperty 
 
 property SyncIniteotid; @(posedge clk) (reset) |-> (d == q) ;endproperty 
 
 property SyncIniteotid; @(posedge clk) (reset) |-> (q == 0) ;endproperty 
 
 property SyncIniteotid; @(posedge clk) (reset) |-> (d == q) ;endproperty 
 