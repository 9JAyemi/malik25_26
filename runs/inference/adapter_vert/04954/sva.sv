property SyncAdderCheckeotid; @(posedge clk) (A) + (B) == (sum_reg1) ;endproperty 
 
 property SyncAddereotid; @(posedge clk) (sum_reg1) == (sum_reg2) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (sum_reg2) == (sum_reg3) ;endproperty 
 
 property SyncAddereotid; @(posedge clk) (A) + (B) == (OUT) ;endproperty 
 