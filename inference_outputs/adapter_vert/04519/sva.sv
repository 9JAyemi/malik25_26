property ResetSynceotid; @(negedge clk_reset_13) (A) |-> (nor1_out) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_13) (C) |-> (nor2_out) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_13) (A) && @(negedge clk_reset_13) (C) |-> (Y) ; endproperty 
 