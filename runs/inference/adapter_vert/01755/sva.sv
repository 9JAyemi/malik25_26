property ResetSynceotid; @(posedge clk) (reset) |-> q == 0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (q1) == 0 && (q2) == 0 && (cin1) == 0 && (cin2) == 0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !reset ) &&  (  select ) |-> q == sum1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !reset ) &&  ( !select ) |-> q == sum2 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !reset ) &&  (  select ) |-> (q1) == d1 && (cin1) == 1'b0 && (q2) == sum1 && (cin2) == cout1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) ( !reset ) &&  ( !select ) |-> (q2) == d2 && (cin2) == 1'b0 && (q1) == sum2 && (cin1) == cout2 ;endproperty 
 