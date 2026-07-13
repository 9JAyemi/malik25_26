property ClockSynceotid; @(posedge clk) (ce) |-> op_reg == ~ip ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (clr) |-> op == 1'b0 ;endproperty 
 