property ResetSynceotid; @(posedge clk) (reset) |-> count_reg == 4'b0 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> count_reg == reg_15 ;endproperty 
 
 