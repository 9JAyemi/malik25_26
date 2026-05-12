property ResetSynceotid; @(negedge clk_reset_14) (X) == (1'b0) |-> (A) == 1'b0 && (SLEEP_B) == 1'b1 ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) (X) != 1'b0 |-> (A) != 1'b0 || (SLEEP_B) != 1'b1 ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) (X) != 1'b1 || (A) != 1'b0 || (SLEEP_B) != 1'b1 ;endproperty 
 