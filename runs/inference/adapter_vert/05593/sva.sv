property ResetSynceotid; @(posedge s_aclk) (AR) |-> Q == 4'b0 ; endproperty 
 
 property SyncCheckeotid; @(posedge s_aclk) (AR) != 1'b1 &&  (E) |-> Q == (Q == 4'b1111) ? 4'b0 : Q + 1; endproperty 
 