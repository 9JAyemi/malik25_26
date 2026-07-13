property XorSynceotid; @(posedge clk_in_16) (a) &&  ( !b ) |->  ( out_comb ) ;endproperty 
 
 property XorSynceotid; @(posedge clk_in_16)  ( !a ) &&  ( b ) |->  ( out_comb ) ;endproperty 
 
 property XorSynceotid; @(posedge clk_in_16) (a) &&  ( b ) |->  ( !out_comb ) ;endproperty 
 
 property XorSynceotid; @(posedge clk_in_16)  ( !a ) &&  ( !b ) |->  ( !out_comb ) ;endproperty 
 