property SyncIneotid; @(posedge clk) (in) != (out) |-> state == UNSTABLE ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (in) != (out) &&  ( debounce_count ) != 0  |-> state == UNSTABLE ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (in) != (out) &&  ( debounce_count ) == 0  |-> state == DEBOUNCE && out == in ;endproperty 
 
 property SyncSafeeotid; @(posedge clk) (in) == (out)  &&  ( state ) == (DEBOUNCE) |-> state == STABLE ;endproperty 
 