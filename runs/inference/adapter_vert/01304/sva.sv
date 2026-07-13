property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0000 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (enable) && ! (reset) |-> count == reg_1 ;endproperty 
 