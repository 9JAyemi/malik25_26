property ResetSynceotid; @(posedge clk) (reset) |-> (product == 0) && (sum == 0) ;endproperty 
 
 property ValidDataeotid; @(posedge clk) ( !reset ) &&  (  sel ) |-> (sum == a + b) ;endproperty 
 
 property ValidDataeotid; @(posedge clk) ( !reset ) &&  ( !sel ) |-> (product == a * b) ;endproperty 
 
 