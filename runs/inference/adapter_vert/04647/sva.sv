property SubSynceotid; @(posedge clk_in_1) (A) - (B) == (Y) ;endproperty 
 
 property SyncSubeotid; @(posedge clk_in_1) (A) != (B) |-> (Y) != 4'bx000 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A) != (B) &&  (  (A) - (B)  != 0 ) |-> (Y) != 4'b0000 ;endproperty 
 