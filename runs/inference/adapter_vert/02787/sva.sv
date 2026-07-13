property InvertOnClockRiseeotid; @(posedge clk_in_1) (binary) |-> (invert) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (invert) |-> (add_one) ;endproperty 
 
 property TwoCompeotid; @(posedge clk_in_1) (add_one) |-> (twos_comp) ;endproperty 
 