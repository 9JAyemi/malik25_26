property AddOneeotid; @(posedge clk_in_1) (A) |-> (temp_sum) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (B) |-> (temp_sum) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  ( 1'b0 ) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  ( 1'b0 ) &&  (B) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) ( 1'b0 ) &&  (A) &&  (B) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) ( 1'b0 ) &&  ( 1'b0 ) &&  ( 1'b0 ) |-> (temp_sum) == (a ) &&  (temp_carry) == (b ) ;endproperty 
 
 