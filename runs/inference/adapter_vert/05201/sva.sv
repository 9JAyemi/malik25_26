property SyncAddOneeotid; @(posedge clk_in_1) (A) |-> (S) ;endproperty 
 
 property SyncCarryeotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) |-> (Cout) ;endproperty 
 
 property SyncAdderCheckeotid; @(posedge clk_in_1) (A) &&  (B) &&  (Cin) &&  (En) |-> (S) ;endproperty 
 