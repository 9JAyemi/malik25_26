property ResetSynceotid; @(posedge CLK) (CLR_B) |-> Q == 0 ;endproperty 
 
 property LoadSynceotid; @(posedge CLK) (LOAD) |-> Q == DATA_IN ;endproperty 
 
 property ClockSynceotid; @(posedge CLK) (Q == MAX_VALUE - 1) |-> Q == 0 ;endproperty 
 
 property SyncCounteotid; @(posedge CLK) (CLR_B) != 1'b1 && (LOAD) != 1'b1 &&  (Q != MAX_VALUE - 1)  |-> Q == reg_14 ;endproperty 
 