property SplitIneotid; @(posedge clk) ( in ) |-> ( out_hi ) == ( in[15:8] ) ; endproperty 
 
 property SplitLoeotid; @(posedge clk) ( in ) |-> ( out_lo ) == ( in[7:0] ) ; endproperty 
 