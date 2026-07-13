property SyncIneotid; @(negedge clk_in_1) (A) |-> (not_A) ; endproperty 
 
 property ValidIneotid; @(negedge clk_in_1) (B) &&  (C) |-> (and_B_C) ; endproperty 
 
 property ValidIneotid; @(negedge clk_in_1) (A) &&  (B) &&  (C) |-> (X) == (1'b0) ; endproperty 
 