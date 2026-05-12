property ResetSynceotid; @(negedge clk_reset_19) (A) == (0) && (B) == (0) |-> (O) == 16'b0000000000000001 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) == (0) && (B) == (1) |-> (O) == 16'b0000000000000010 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) == (1) && (B) == (0) |-> (O) == 16'b0000000000000100 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) == (1) && (B) == (1) |-> (O) == 16'b0000000000001000 ; endproperty 
 