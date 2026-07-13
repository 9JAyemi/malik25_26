property ClockSynceotid; @(posedge clk_in_17) (a) |-> (a_gt_b) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_17) (b) |-> (a_lt_b) ; endproperty 
 
 property SyncEqeotid; @(posedge clk_in_17) (a) == (b) |-> (a_eq_b) ; endproperty 
 