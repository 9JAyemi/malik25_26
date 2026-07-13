property HighPrioSynceotid; @(posedge clk_in_1) (in) == (7'b1110000) |-> (out) == 2'b00 ; endproperty 
 
 property HighPrioSynceotid; @(posedge clk_in_1) (in) == (6'b110100) |-> (out) == 2'b01 ; endproperty 
 
 property HighPrioSynceotid; @(posedge clk_in_1) (in) == (5'b10110) |-> (out) == 2'b10 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (in) == (4'b0111) |-> (out) == 2'b11 ; endproperty 
 
 property SafeStarteotid; @(posedge clk_in_1) (in) != 7'b1110000 && @(posedge clk_in_1) (in) != 6'b110100 && @(posedge clk_in_1) (in) != 5'b10110 && @(posedge clk_in_1) (in) != 4'b0111  |-> (out) == 2'b00; endproperty 
 