property BitwiseAndeotid; @(posedge clk_in_1) (a) && (b) |-> and_out == (a) && (b) ; endproperty 
 
 property BitwiseOrEeotid; @(posedge clk_in_1) (a) || (b) |-> or_out == (a) || (b) ; endproperty 
 
 property BitwiseXOReotid; @(posedge clk_in_1) (a) != (b) |-> xor_out == (a) != (b) ; endproperty 
 
 property BitwiseNotEqeotid; @(posedge clk_in_1)  (a)  !=  (not_out)  |-> 1'b1 ; endproperty 
 