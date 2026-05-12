property ResetSynceotid; @(negedge clk_reset_19) (a) |-> (sum) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (b) |-> (sum) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (a) && @(negedge clk_reset_19) (b) |-> (carry_out) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (a) && @(negedge clk_reset_19) (b) &&  (  !(a) && !(b)  ) |-> !(carry_out) ;endproperty 
 