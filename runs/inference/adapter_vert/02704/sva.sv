property ResetSynceotid; @(negedge clk_reset_19) (Y) |-> (and0_out_Y) && (nor0_out); endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (and0_out_Y) |-> (C_N) && (nor0_out); endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (buf0) == (and0_out_Y); endproperty 
 