property AdderSynceotid; @(posedge clk_in_1) ( A ) != (  B ) |-> ( S ) != (  Ci ) ;endproperty 
 
 property ValidAddereotid; @(posedge clk_in_1) ( A ) != (  B ) &&  (  Ci ) |-> ( S ) != (  Ci ) ;endproperty 
 
 property CarrySynceotid; @(posedge clk_in_1) ( A ) == (  B ) &&  (  Ci ) |-> ( Co ) ;endproperty 
 
 property ValidAddereotid; @(posedge clk_in_1) ( A ) == (  B )  &&  (  Ci ) !=  (  S ) |-> ( Co ) ;endproperty 
 