property ClockSynceotid; @(posedge clk_in_15) (or0_out) == (1'b1) &&  (A1 == 1'b1) &&  (A2 == 1'b1) ;endproperty 
 property ValidDataeotid; @(posedge clk_in_15) (and0_out) == (1'b1) &&  (or0_out == 1'b1) &&  (B1 == 1'b1) &&  (C1 == 1'b1) ;endproperty 
 property ValidDataeotid; @(posedge clk_in_15) (not0_out) == (1'b0) &&  (and0_out == 1'b1) ;endproperty 
 property ValidDataeotid; @(posedge clk_in_15) (Y) == (1'b1) &&  (not0_out == 1'b0) ;endproperty 
 