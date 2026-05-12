property SleepSynceotid; @(posedge clk_osc_19) (X) |-> (A) && (sleepn); endproperty 
 
 property SleepSynceotid; @(posedge clk_osc_19) (X) &&  (A) &&  (SLEEP) |-> ! (sleepn) ; endproperty 
 
 property SleepSynceotid; @(posedge clk_osc_19) (X) &&  (A) &&  ! (SLEEP) |->  (sleepn) ; endproperty 
 