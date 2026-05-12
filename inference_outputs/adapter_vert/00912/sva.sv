property ResetSynceotid; @(posedge CLK) (CLR) |-> (Q == 4'b0000) && (Q_next == 4'b0000) ;endproperty 
 
 property LoadSynceotid; @(posedge CLK) (LOAD) && !(CLR)  |-> (Q == D) && (Q_next == D) ;endproperty 
 
 property ShiftSynceotid; @(posedge CLK) ( !LOAD ) && !(CLR)  |-> (Q == {Q[2:0], D[3]}) && (Q_next == {Q[2:0], D[3]});endproperty 
 