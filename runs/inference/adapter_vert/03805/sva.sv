property ClockSynceotid; @(posedge clk_in_14) (OE) |-> (Z) == 2'b10 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (OE) != 1'b1  |-> (Z) == 2'b01; endproperty 
 