property ResetSynceotid; @(posedge CLK) ( !AR ) |-> Q_reg == 7'b0000000 ; endproperty 
 
 property SyncLoadeotid; @(posedge CLK) (  AR ) && (  E ) |-> Q_reg == data_14 ; endproperty 
 