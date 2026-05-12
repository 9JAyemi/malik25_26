property AddSynceotid; @(posedge clk_in_1) (mode) == (0) |-> (Y) == (A + B) ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (mode) != 0  |-> (Y) == (A +  ( ~B ) + 1) ; endproperty 
 