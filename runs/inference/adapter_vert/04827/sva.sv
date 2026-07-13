property ClockSynceotid; @(posedge clk_in_1) (sel0) |-> (out) == (in0) ; endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (sel0) &&  (  !(sel0)  &&  (sel1)  ) |-> (out) == (in2) ; endproperty 
 
 property SyncOuteotid; @(posedge clk_in_1) (  !(sel0)  &&  !(sel1)  ) |-> (out) == (in3) ; endproperty 
 