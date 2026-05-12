property CarrySynceotid; @(posedge clk_in_1) (a) |-> (a_15) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) (b) |-> (b_15) ;endproperty 
 
 property SyncAddereotid; @(posedge clk_in_1) (a) &&  (b) &&  ( 1'b0 ) |-> (sum) == (  {c_3, c_2, c_1, c_0, a_15: a_4} ) ;endproperty 
 
 property SyncCarryeotid; @(posedge clk_in_1) (a) &&  (b) &&  ( 1'b0 ) |-> (cout) == (  c_3 ) ;endproperty 
 