property AddOneeotid; @(posedge clk_in_1) (A) + (B) == (temp_sum) ; endproperty 
 
 property CarryCheckeotid; @(posedge clk_in_1) (temp_sum) == (8'bxxxxxx1x) |-> (carry) == (1'b1) ; endproperty 
 
 property ValidSumeotid; @(posedge clk_in_1) (temp_sum) != 8'bxxxxxx1x |-> (carry) == (1'b0) ; endproperty 
 