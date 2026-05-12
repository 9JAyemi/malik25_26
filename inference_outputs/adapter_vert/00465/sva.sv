property ResetSynceotid; @(posedge clk) (reset) |-> count == 2'b00 ;endproperty 
 
 property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> count == reg_1 ;endproperty 
 
 property SyncCtrleotid; @(posedge clk) (reset) != 1'b1 &&  !(enable)  |-> count == reg_1 ;endproperty 
 