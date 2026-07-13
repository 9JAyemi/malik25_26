property Clockwiseeotid; @(posedge clock) ( a_in ) |-> ( out == a_in | b_in ) ; endproperty 
 
 property SyncOr; @(posedge clock) ( b_in ) |-> ( out == a_in | b_in ) ; endproperty 
 
 property SyncOrEqeotid; @(posedge clock) ( a_in ) &&  (  b_in ) |-> ( out == a_in | b_in ) ; endproperty 
 