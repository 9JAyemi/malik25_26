property ClockSynceotid; @(posedge clk_in_1) (X) == (or0_out_X) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (not0_out) == ( ! ( D_N ) ) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (or0_out_X) == ( not0_out && C && B && A ) ;endproperty 
 