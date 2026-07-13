property ResetSynceotid; @(posedge clock) (reset) |-> (d == io_init) ;endproperty 
 
 property EnableSynceotid; @(posedge clock) ( !reset ) &&  (  io_enable ) |-> (d == io_in) ;endproperty 
 