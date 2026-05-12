property ResetSynceotid; @(posedge CLK) (RST) |-> ENCLK == 0 ;endproperty 
 
 property EnableSynceotid; @(posedge CLK) (RST) != 1'b1 &&  (TE) |-> ENCLK == EN ;endproperty 
 