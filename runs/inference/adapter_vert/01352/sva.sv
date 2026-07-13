property LoadSynceotid; @(posedge load) (load) |-> (out == (in >> 1) ^ in) && (valid == 1) ; endproperty 
 
 property ValidOnLoador; @(posedge load) (load) |-> (valid == 1) ; endproperty 
 
 property ValidOnLoador; @(posedge load) ! (load)  |-> (valid == 0) ; endproperty 
 