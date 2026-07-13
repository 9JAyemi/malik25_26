property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b000) |-> (out) == 8'b00000001 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b001) |-> (out) == 8'b00000010 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b010) |-> (out) == 8'b00000100 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b011) |-> (out) == 8'b00001000 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b100) |-> (out) == 8'b00010000 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b101) |-> (out) == 8'b00100000 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b110) |-> (out) == 8'b01000000 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b111) |-> (out) == 8'b10000000 ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (in) != 3'b000 && @(negedge clk_reset_19) (in) != 3'b001 && @(negedge clk_reset_19) (in) != 3'b010 && @(negedge clk_reset_19) (in) != 3'b011 && @(negedge clk_reset_19) (in) != 3'b100 && @(negedge clk_reset_19) (in) != 3'b101 && @(negedge clk_reset_19) (in) != 3'b110 && @(negedge clk_reset_19) (in) != 3'b111  |-> (out) == 8'b00000000; endproperty 
 