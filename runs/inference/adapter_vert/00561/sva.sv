property AddSynceotid; @(posedge clk_in_1) (op) == (0) |-> (result) == (a + b) ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (op) != 0  |-> (result) == (a - b) ; endproperty 
 