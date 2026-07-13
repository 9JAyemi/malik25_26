property Multiplyeotid; @(posedge clk_in_1) (num1) * (num2) == (product) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (num1) != 8'hff &&  (num2) != 8'hff |-> (product) != 16'hffff ;endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (num1) != 8'h00 &&  (num2) != 8'h00 |-> (product) != 16'h0000 ;endproperty 
 