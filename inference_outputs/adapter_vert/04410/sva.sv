property ResetSynceotid; @(posedge clk) (aclr) |-> mem == 6'h0 ;endproperty 
 
 property SyncIneotid; @(posedge clk) (aclr) |-> dout == 1'b0 ;endproperty 
 
 property SyncIneotid; @(posedge clk) ( !aclr ) |-> mem == mem ;endproperty 
 
 property SyncIneotid; @(posedge clk) ( !aclr ) |-> dout == mem ;endproperty 
 