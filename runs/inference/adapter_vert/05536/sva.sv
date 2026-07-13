property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (load) |-> count == data_in ;endproperty 
 
 property IncrCtrleotid; @(posedge clk) (up_down) && ! (reset) && ! (load)  |-> count == reg_13 ;endproperty 
 
 property DecrCtrleotid; @(posedge clk) ! (up_down) && ! (reset) && ! (load)  |-> count == reg_15 ;endproperty 
 