property AdderSynceotid; @(posedge clk_in_1) (a) |-> (sum) == (a + b + cin) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |->  (cout) ==  (sum[4]) ;endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |->  (s) ==  (sum[3:0]) ;endproperty 
 