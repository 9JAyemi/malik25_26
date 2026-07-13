property ResetSynceotid; @(posedge CLK) (reset) |-> count == 4'b0 ;endproperty 
 
 property EnableSynceotid; @(posedge CLK) (reset) != 1'b1 &&  (enable) |-> count == reg_15 ;endproperty 
 