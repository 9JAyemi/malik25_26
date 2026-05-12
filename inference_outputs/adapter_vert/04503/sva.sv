property ClockSynceotid; @(posedge clk_in_18) (COUT) |-> (SUM) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) |-> (xor0_out_SUM) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) |-> (SUM) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) |-> (a_b) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) |-> (a_ci) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) |-> (b_ci) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_18) (A) && (  B ) &&  (  CI ) &&  (  xor0_out_SUM ) &&  (  a_b ) &&  (  a_ci ) &&  (  b_ci ) |-> (COUT) ;endproperty 
 