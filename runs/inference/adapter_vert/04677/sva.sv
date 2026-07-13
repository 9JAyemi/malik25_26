property SyncXorCheckeotid; @(posedge clk_in_17) ( a ) != ( b ) |-> ( y ) != ( a ); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) ( a ) != ( b ) |-> ( w1 ) == ( 1'b1 ); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) ( a ) != ( b ) |-> ( w2 ) == ( 1'b0 ); endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_17) ( a ) != ( b ) |-> ( w3 ) == ( 1'b0 ); endproperty 
 