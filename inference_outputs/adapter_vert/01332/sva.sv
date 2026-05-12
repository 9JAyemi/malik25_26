property AddSynceotid; @(posedge clk_in_1) (SUB) |-> (OUT) == (B - A) ; endproperty 
 
 property AddSynceotid; @(posedge clk_in_1) (SUB) != 1'b1  |-> (OUT) == (A + B) ; endproperty 
 