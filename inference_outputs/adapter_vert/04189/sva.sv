property ResetSynceotid; @(posedge CLK) (RST) |-> reg1 == 4'b0 && reg2 == 4'b0 && reg3 == 4'b0 && reg4 == 4'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge CLK) (RST) != 1'b1 &&  (LD) |-> reg1 == D && reg2 == reg1 && reg3 == reg2 && reg4 == reg3 ;endproperty 
 
 property SyncCheckeotid; @(posedge CLK) (RST) != 1'b1 &&  !(LD)  |-> reg1 == reg2 && reg2 == reg3 && reg3 == reg4 ;endproperty 
 