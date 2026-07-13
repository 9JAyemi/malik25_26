property SyncDataeotid; @(posedge clk) (en && carrier) |-> out == {n{modulated}} ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (en && carrier) |-> out != 0 ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) ! (en && carrier)  |-> out == 0; endproperty 
 