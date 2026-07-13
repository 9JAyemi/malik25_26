property SyncIneotid; @(posedge clk_in_15) (X) |-> (and0_out_X) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_15) (and0_out_X) |-> (X) ;endproperty 
 