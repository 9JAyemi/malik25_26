property SyncIneotid; @(posedge clk_in_14) (free3) &&  (tm_count == 2'b11) |-> fifowp_inc == 4'b0011 ;endproperty 
 
 property ValidWriteeotid; @(posedge clk_in_14) (free2) &&  (tm_count >= 2'b10) |-> fifowp_inc == 4'b0010 ;endproperty 
 
 property ValidTxeotid; @(posedge clk_in_14) (tm_count) &&  (tm_count >= 2'b01) |-> fifowp_inc == 4'b0001 ;endproperty 
 
 property ValidWriteeotid; @(posedge clk_in_14) ( !free3 ) &&  ( !free2 ) &&  ( tm_count < 2'b01 ) |-> fifowp_inc == 4'b0000 ;endproperty 
 