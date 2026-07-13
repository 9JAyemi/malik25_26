property ResetSynceotid; @(posedge CLK) (CLR) |-> (Q1) == 4'b0000 ;endproperty 
 
 property LoadSynceotid; @(posedge CLK) (CLR) != 1'b1 && (LD1) |-> (Q1) ==  (D1) ;endproperty 
 
 property ShiftSynceotid; @(posedge CLK) (CLR) != 1'b1 && !(LD1)  |-> (Q1) ==  ({Q1[2:0], Q1[3]}) ;endproperty 
 
 property SyncAddereotid; @(posedge CLK) (CLR)  &&  (LD1)  &&  (LD2) |->  (sum) ==  (D1 + D2) ;endproperty 
 
 property SyncCheckeotid; @(posedge CLK) (CLR)  &&  (LD1)  &&  !(LD2) |->  (Q1) ==  (D1) ;endproperty 
 
 property SyncCheckeotid; @(posedge CLK) (CLR)  &&  !(LD1)  &&  (LD2) |->  (Q1) ==  ({Q1[2:0], Q1[3]}) ;endproperty 
 
 property SyncCheckeotid; @(posedge CLK) (CLR)  &&  !(LD1)  &&  !(LD2)  |->  (Q1) ==  4'b0000 ;endproperty 
 