property ClockSynceotid; @(posedge clk) (en) |-> data_out == data_in ; endproperty 
 
 property ClockGateeotid; @(posedge clk) (en) != 1'b1  |-> data_out == 1'b0; endproperty 
 