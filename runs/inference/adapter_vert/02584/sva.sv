property AdderSynceotid; @(posedge clk_in_1) ( A ) |-> ( n1 ) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) ( B ) |-> ( n1 ) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) ( Ci ) |-> ( n1 ) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) ( n1 ) == ( 4'bxxxx ) |-> ( S ) == ( n1 ) ; endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) ( n1 ) == ( 4'bxxxx ) |-> ( Co ) == ( n7 ) ; endproperty 
 