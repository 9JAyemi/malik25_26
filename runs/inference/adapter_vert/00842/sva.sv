property AddOneeotid; @(posedge clk_in_14) (a) |-> (sum) ;endproperty 
 
 property AddOneeotid; @(posedge clk_in_14) (b) |-> (sum) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (a) &&  (b) &&  (  !cin ) |->  (sum) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (a) &&  (  !b ) &&  (  !cin ) |->  (sum) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (  !a ) &&  (b) &&  (  !cin ) |->  (sum) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (  !a ) &&  (  !b ) &&  (  !cin ) |->  (sum) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (a) &&  (b) &&  (  !cin ) |->  (cout) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (a) &&  (  !b ) &&  (  !cin ) |->  (cout) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (  !a ) &&  (b) &&  (  !cin ) |->  (cout) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_14) (  !a ) &&  (  !b ) &&  (  !cin ) |->  (cout) ;endproperty 
 
 