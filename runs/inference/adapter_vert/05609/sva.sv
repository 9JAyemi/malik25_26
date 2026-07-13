property ValidIneotid; @(posedge clk_in_1) (A1) && (A2) &&  ( !B1_N ) |->  (X) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (A1) && (A2) &&  ( C1 ) |->  (and2_out) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (A1) && (A2) &&  ( !B1_N ) &&  ( C1 ) |->  (X) ;endproperty 
 