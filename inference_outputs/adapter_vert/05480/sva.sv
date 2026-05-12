property AdderSynceotid; @(posedge clk_in_1) (A) |-> (C) == (sum); endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) |-> (CO) == (1'b1); endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (A) &&  (B) ||  (A) &&  (!B) ||  (!A) &&  (B)  |-> (C) != 7'b0000000 ; endproperty 
 