property ResetOnInputeotid; @(negedge clk_reset_15) (input_value) == (5) |-> (output_value) == 2'b00 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_15) (input_value) >= 10  |-> (output_value) == 2'b10 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_15) (input_value) != 5 && (input_value) < 10  |-> (output_value) == 2'b01 ; endproperty 
 