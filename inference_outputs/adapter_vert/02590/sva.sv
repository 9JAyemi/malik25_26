property ClockSynceotid; @(negedge clk) (sel) |-> q_reg == d2 ; endproperty 
 
 property DataSynceotid; @(negedge clk) (sel) |-> data_15 == reg_1 ; endproperty 
 
 property DataSynceotid; @(negedge clk) ! (sel) |-> q_reg == d1 ; endproperty 
 
 property SyncDataeotid; @(negedge clk) ! (sel) |-> data_15 == reg_1 ; endproperty 
 