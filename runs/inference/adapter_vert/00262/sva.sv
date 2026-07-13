property ValidInputeotid; @(posedge clk_in_1) (input1) |-> (output1) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (input2) |-> (output1) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (input3) |-> (output1) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (input4) |-> (output1) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (input1) && @(posedge clk_in_1) (input2) && @(posedge clk_in_1) (input3) && @(posedge clk_in_1) (input4) |-> (output1) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (input1) || @(posedge clk_in_1) (input2) || @(posedge clk_in_1) (input3) || @(posedge clk_in_1) (input4) |-> (output1) ; endproperty 
 