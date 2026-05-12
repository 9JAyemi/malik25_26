property BitwiseOReotid; @(posedge clk_in_1) (a) |-> (or_result) ;endproperty 
 
 property TwoComplementeotid; @(posedge clk_in_1) (a) |-> (twos_comp_result) ;endproperty 
 
 property DiffCheckeotid; @(posedge clk_in_1) (a) |-> (diff) ;endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (or_result) |-> (out) ;endproperty 
 