property EnableSynceotid; @(posedge clk) (se) |-> q == si ; endproperty 
 
 property EnableSynceotid; @(posedge clk) (se) != 1'b1 &&  (en)  |-> q == din ; endproperty 
 
 property SyncOuteotid; @(posedge clk) (se) != 1'b1 &&  !(en)  |-> so == q ; endproperty 
 