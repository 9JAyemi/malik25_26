property GreaterThaneotid; @(posedge clk_in_1) (in1) > (in2) |-> (out) == 2'b01 ; endproperty 
 
 property EqualCheckeotid; @(posedge clk_in_1) (in1) == (in2) |-> (out) == 2'b00 ; endproperty 
 
 property LessThaneotid; @(posedge clk_in_1) (in1) < (in2) |-> (out) == 2'b10 ; endproperty 
 