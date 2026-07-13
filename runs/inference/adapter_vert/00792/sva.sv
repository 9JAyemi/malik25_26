property XorSynceotid; @(posedge clk_in_15) (a) != (b) |-> (out_comb_logic) == (a ^ b) ;endproperty 
 
 property SyncEqeotid; @(posedge clk_in_15) (a) == (b) &&  (out_comb_logic) != (a ^ b) |-> err_14 ;endproperty 
 