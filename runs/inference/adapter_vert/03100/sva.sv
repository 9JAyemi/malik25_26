property SyncAddOneeotid; @(posedge clk) (a) |-> (sum1) ;endproperty 
 
 property SyncAddOneeotid; @(posedge clk) (a) &&  (b) &&  (sub) |-> (sum2) ;endproperty 
 
 property SyncXorCheckeotid; @(posedge clk) (a) &&  (b) &&  (sub) |-> (xor_b) ;endproperty 
 
 property SyncAddOneeotid; @(posedge clk) (a) &&  (b) &&  (sub) |-> (sum2) ;endproperty 
 
 