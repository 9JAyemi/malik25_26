property ClockSynceotid; @(posedge clk_in_13) (SEL) |-> (Y) == (B) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_13) (SEL) != 1'b1  |-> (Y) == (A) ; endproperty 
 