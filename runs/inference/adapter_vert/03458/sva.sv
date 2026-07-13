property AddOneeotid; @(posedge clk_in_1) (a) != (b) && (carry_in) |-> (sum) != (a) && (sum) != (b); endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (a) != (b) && (carry_in) &&  (  (a) != (b)  && (carry_in) ) |-> (carry_out) == 1'b1 ; endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (a) == (b) && (carry_in) |-> (sum) == 1'b1 ; endproperty 
 
 property SyncCarryeotid; @(posedge clk_in_1) (a) != (b) && !(carry_in)  |-> (sum) != (a) && (sum) != (b); endproperty 
 
 property SyncCarryeotid; @(posedge clk_in_1) (a) != (b) && !(carry_in) &&  (  (a) != (b)  && !(carry_in) ) |-> (carry_out) == 1'b0 ; endproperty 
 
 property SyncCarryeotid; @(posedge clk_in_1) (a) == (b) && !(carry_in) |-> (sum) == 1'b0 ; endproperty 
 