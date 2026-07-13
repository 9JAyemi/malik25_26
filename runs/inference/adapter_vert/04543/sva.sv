property SyncIneotid; @(posedge clk_in_17) (B) |-> (not0_out) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_17) (A_N) |-> (not1_out) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_17) (B) &&  (A_N) |-> (and0_out) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_17) (B) &&  (A_N) |-> (Y) ;endproperty 
 