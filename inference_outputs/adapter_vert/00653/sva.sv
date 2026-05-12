property ValidInputeotid; @(posedge clk_in_19) (A) && (B) |-> (and0_out) ;endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (C) && (D) |-> (and1_out) ;endproperty 
 
 property ValidInputeotid; @(posedge clk_in_19) (and0_out) && (and1_out) |-> (X) ;endproperty 
 