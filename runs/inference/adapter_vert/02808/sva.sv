property ClockSynceotid; @(posedge clk_in_14) (in) |-> (out_hi) ; endproperty 
 
 property SyncLoadeotid; @(posedge clk_in_14) (in) |-> (out_lo) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (in) &&  (  (in[15:14] != 2'b00) &&  (in[15:14] != 2'b11) ) |-> (out_hi) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_14) (in) &&  (  (in[15:14] != 2'b00) &&  (in[15:14] != 2'b11) ) |-> (out_lo) ; endproperty 
 