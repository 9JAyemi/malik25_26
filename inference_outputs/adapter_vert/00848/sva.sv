property SyncIneotid; @(posedge clock) (i_settings) |-> (o_dataout == i_register_settings) ;endproperty 
 
 property ValidDataeotid; @(posedge clock) (i_settings) |-> (o_dataout_valid == i_datain_valid) ;endproperty 
 
 property SyncCheckeotid; @(posedge clock) (i_settings) |-> (o_datain_stall == i_dataout_stall) ;endproperty 
 