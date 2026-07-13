property ClockSynceotid; @(posedge clk_in_14) (X) == (or0_out_X) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_14) (D_N) != (C_N) |-> (nand0_out) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_14) (B) || (A) || (nand0_out) |-> (or0_out_X) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_in_14) (or0_out_X) == (X) ;endproperty 
 