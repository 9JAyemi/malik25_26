property ClockSynceotid; @(posedge clk_in_17) (and0_out) == (A1) && (A2) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_17) (or0_out_X) == (and0_out) || (C1) || (B1) ;endproperty 
 
 property ValidXeotid; @(posedge clk_in_17) (X) == (or0_out_X) ;endproperty 
 