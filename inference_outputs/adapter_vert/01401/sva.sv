property LoadSynceotid; @(posedge clk) (load) |-> shift_reg == data_in ;endproperty 
 
 property ShiftSynceotid; @(posedge clk) (load) != 1'b1  |-> shift_reg == data_out ;endproperty 
 