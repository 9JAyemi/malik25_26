property ResetSynceotid; @(posedge clk) (reset) |-> (sum_output) == 0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (product_output) == 0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (difference_output) == 0 ;endproperty 
 