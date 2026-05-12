property ResetSynceotid; @(posedge clk) (se) |-> q == si ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (se) != 1'b1 && (rst) |-> q == 1'b0 ; endproperty 
 
 property ValidDataeotid; @(posedge clk) (se) != 1'b1 && !(rst) && (en) |-> q == din ; endproperty 
 
 property SyncOuteotid;  @(posedge clk) (se) != 1'b1 && !(rst) && !(en)  |-> so == q; endproperty 
 