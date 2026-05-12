property AdderSynceotid; @(posedge clk_in_1) (A) |-> (sum) ; endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (cin) |->  (cout) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (cin) |->  (sum) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (cin) &&  (  ! (A)  &&  ! (B)  &&  ! (cin) ) |->  (  ! (sum)  &&  ! (cout) ) ; endproperty 
 