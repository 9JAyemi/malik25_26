property SyncAndeotid; @(posedge clk_in_1) (A) and (B) |-> (AB); endproperty 
 
 property SyncAndeotid; @(posedge clk_in_1) (C) and (D) |-> (CD); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (AB) and (CD) |-> (ABCD); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (A) and (B) and (C) and (D) == 1'b1 |-> (Z) == 1'b1 ; endproperty 
 