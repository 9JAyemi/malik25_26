property EnableSynceotid; @(posedge CLK) (EN) |-> ENCLK == TE ; endproperty 
 
 property ClockGateeotid; @(posedge CLK) (EN) != 1'b1  |-> ENCLK == 0; endproperty 
 