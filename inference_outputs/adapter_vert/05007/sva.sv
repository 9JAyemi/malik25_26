property SyncOneotid; @(posedge clk_in_1) (a) |-> (temp1) ;endproperty 
 
 property SyncOneotid; @(posedge clk_in_1) (b) |-> (temp2) ;endproperty 
 
 property ValidOuteotid; @(posedge clk_in_1) (temp1) &&  (temp2) |->  (out) ;endproperty 
 