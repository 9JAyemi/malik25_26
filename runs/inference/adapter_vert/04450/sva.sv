property ClockSynceotid; @(posedge CLK) (DE) |-> Q == D ; endproperty 
 
 property SyncLoadeotid; @(posedge CLK) (DE) != 1'b1 && (SCE) |-> Q == SCD ; endproperty 
 