property GreaterThaneotid; @(posedge clk_in_15) (A) > (B) |-> result == 2'b01 ; endproperty 
 
 property LessThaneotid; @(posedge clk_in_15) (A) < (B) |-> result == 2'b10 ; endproperty 
 
 property EqualToeotid; @(posedge clk_in_15) (A) == (B) |-> result == 2'b00 ; endproperty 
 