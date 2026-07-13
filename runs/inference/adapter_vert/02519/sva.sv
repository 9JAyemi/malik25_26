property AddSynceotid; @(posedge clk_in_15) (C) == (1'b1) |-> (Q) == (A - B) ; endproperty 
 
 property AddSynceotid; @(posedge clk_in_15) (C) != 1'b1  |-> (Q) == (A + B) ; endproperty 
 