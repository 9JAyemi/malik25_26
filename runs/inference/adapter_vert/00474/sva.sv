property SyncXorCheckeotid; @(posedge clk_in_19) ( Sgn_X ) != ( Sgn_Y ) |-> ( Sgn_Info ) == ( Sgn_X ^ Sgn_Y );endproperty 
 
 property SyncXorCheckeotid; @(posedge clk_in_19) ( Sgn_X ) != ( Sgn_Y ) &&  (  !cfg_14 ) |-> ( Sgn_Info ) == ( Sgn_X ^ Sgn_Y );endproperty 
 
 property SyncXorCheckeotid; @(posedge clk_in_19) ( Sgn_X ) != ( Sgn_Y ) &&  (  cfg_14 ) |-> ( Sgn_Info ) != ( Sgn_X ^ Sgn_Y );endproperty 
 