property EqualOnClockeotid; @(posedge clk_in_15) (A) == (B) |-> (EQ) == 1'b1 ; endproperty 
 
 property GreaterThaneotid; @(posedge clk_in_15) (A) > (B) |-> (GT) == 1'b1 ; endproperty 
 
 property LessThaneotid; @(posedge clk_in_15) (A) < (B) |-> (LT) == 1'b1 ; endproperty 
 