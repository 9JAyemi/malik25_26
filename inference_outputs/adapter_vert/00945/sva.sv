property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (0) |-> output_1 == 0 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (1) |-> output_1 == input_3 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (2) |-> output_1 == input_4 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (3) |-> output_1 == input_5 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (4) |-> output_1 == input_6 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (5) |-> output_1 == input_7 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (6) |-> output_1 == input_8 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (7) |-> output_1 == input_2 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (input_1) != 7'b0xx000x |-> output_1 == 0 ; endproperty 
 