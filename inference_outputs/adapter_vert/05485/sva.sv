property ClockSynceotid; @(posedge clk_in_1) (SEL) |-> (Y) == (A) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (SEL) != 0 |-> (Y) == (B) ; endproperty 
 