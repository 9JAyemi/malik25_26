property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable)  |-> count == reg_14 ;endproperty 
 