property ResetSynceotid; @(posedge clk_in_1) (reset) |-> (result) == (4'b0); endproperty 
 
 property ValidOpOnRiseeotid; @(posedge clk_in_1) (reset) != 1'b1 &&  (op) |-> (result) == (num1 - num2); endproperty 
 
 property ValidOpOnRiseeotid; @(posedge clk_in_1) (reset) != 1'b1 &&  !(op)  |-> (result) == (num1 + num2); endproperty 
 