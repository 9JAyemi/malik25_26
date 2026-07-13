property AddOneeotid; @(posedge clk_in_1) (A) |-> (SUM) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (B) |-> (SUM) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  ( 1'b0 ) |->  (SUM)  &&  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  1'b0  ) |->  (SUM)  &&  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (  B  ) &&  (  1'b0  ) |->  (SUM)  &&  (COUT) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (  A  ) &&  (  B  ) &&  (  1'b0  ) |->  (SUM)  &&  (COUT) ;endproperty 
 