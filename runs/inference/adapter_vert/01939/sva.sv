property SyncCheckeotid; @(posedge clk_in_1) (A1) && (A2) |-> (and1_out) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (B1) && (B2) |-> (and2_out) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (B1) && (B2) |-> (not1_out) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A1) && (A2) &&  (B1) && (B2)  |-> (X) == (and1_out && not1_out) ;endproperty 
 