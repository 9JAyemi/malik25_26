property ResetSynceotid; @(posedge clk) (clr) |-> op_reg == 1'b0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (clr) != 1'b1 &&  (ce)  |-> op_reg == 1'b1 ;endproperty 
 
 