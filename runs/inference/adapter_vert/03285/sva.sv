property ResetSynceotid; @(posedge clk) (reset) |-> (q) == (3'b000) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (reset) != 1'b1 |-> (q) == (q << 1) ;endproperty 
 
 