property SyncIneotid; @(posedge clk_in_1) (A) && (B) && (C) |-> (Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A) && (B) && (!C) |-> !(Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A) && (!B) && (C) |-> !(Y) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (!A) && (B) && (C) |-> !(Y) ;endproperty 
 