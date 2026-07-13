property ResetSynceotid; @(posedge CLK) (RST) |-> (Q) == 1'b0 && (QN) == 1'b1 ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) (RST) |-> (Q) != (D) && (Q) != (QN) ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) ! (RST)  |-> (Q) == 1'b0 && (QN) == 1'b1; endproperty 
 