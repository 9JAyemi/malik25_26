property ResetSynceotid; @(posedge CK) (RST) |-> (Q) == 4'b0 ;endproperty 
 
 property SyncIncrseotid; @(posedge CK) (RST) != 1'b1  |-> (Q) == (Q + 1) ;endproperty 
 