property SyncIneotid; @(posedge clk_in_15) (i_bus1) && (i_bus2) |-> (o_bus) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_15) (i_bus1) && !(i_bus2) |-> !(o_bus) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_15) !(i_bus1) && (i_bus2) |-> !(o_bus) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_15) !(i_bus1) && !(i_bus2) |-> !(o_bus) ;endproperty 
 