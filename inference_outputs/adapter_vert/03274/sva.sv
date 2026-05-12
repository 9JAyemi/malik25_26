property ClockResetSynceotid; @(posedge C) (R) |-> Q == D ; endproperty 
 
 property ResetSynceotid; @(posedge C) (R) |-> Q == 1'b0 ; endproperty 
 