property AddSynceotid; @(posedge clk_in_1) (A) |-> (add) == (A + B) ;endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (A) |-> (sub) == (A - B) ;endproperty 
 
 property MultSynceotid; @(posedge clk_in_1) (A) |-> (mul) == (A * B) ;endproperty 
 
 property DivSynceotid; @(posedge clk_in_1) (A) &&  (  (B) != 7'b0000000  ) |-> (div) == (A / B) ;endproperty 
 