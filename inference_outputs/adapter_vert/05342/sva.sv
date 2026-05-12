property SyncAddereotid; @(posedge clk_in_11) ( in1 ) + ( in2 ) == ( sum ) ; endproperty 
 
 property MaxSynceotid; @(posedge clk_in_11) ( out ) == ( sum ) ; endproperty 
 
 property MaxSynceotid; @(posedge clk_in_11) ( max_out ) == (  ( out ) > ( sum )  ? ( out ) : ( sum )  ) ; endproperty 
 