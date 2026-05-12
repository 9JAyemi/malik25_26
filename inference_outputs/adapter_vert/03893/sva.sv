property AddOneeotid; @(posedge clk_in_1) (A) |-> (SUM) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (B) |-> (SUM) ; endproperty 
 
 property AddOneeotid; @(posedge clk_in_1) (A) &&  (B) &&  (  !CARRY_IN ) |->  (SUM)  &&  (  !CARRY_OUT ) ; endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (  CARRY_IN ) ||  (  !A ) &&  (B) &&  (  !CARRY_IN ) ||  (  A ) &&  (  !B ) &&  (  CARRY_IN ) == (  CARRY_OUT ) ; endproperty 
 