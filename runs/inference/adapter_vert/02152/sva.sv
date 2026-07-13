property ClockSynceotid; @(posedge clk) (in) |-> (out == 1'b1) ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (in) != 1'b1  |-> (out == 1'b0) ; endproperty 
 