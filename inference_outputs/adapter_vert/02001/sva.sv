property SyncCheckeotid; @(posedge clk_in_17) (A) |-> (inputs) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) (B) |-> (inputs) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) (C) |-> (inputs) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) (D_N) |-> (inputs) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_17) (inputs) != 4'b0000 |->  (Y) == 1'b1 ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_17) (inputs) != 4'b0000 |->  (Y) != 1'b0 ;endproperty 
 