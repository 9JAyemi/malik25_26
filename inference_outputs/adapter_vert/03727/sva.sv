property SyncIneotid; @(posedge mdio_mdc) ( current_state ) == ( IDLE ) &&  (  preamble == 1 && mdio_in_w == 0 ) |-> ( next_state ) == ( ACQUIRE ) ;endproperty 
 property SyncDataeotid; @(posedge mdio_mdc) ( current_state ) == ( IDLE ) &&  (  !(  preamble == 1 && mdio_in_w == 0 )  ) |-> ( next_state ) == ( IDLE ) ;endproperty 
 property SyncDataeotid; @(posedge mdio_mdc) ( current_state ) == ( ACQUIRE ) &&  (  data_counter == 6'h1f ) |-> ( next_state ) == ( IDLE ) ;endproperty 
 property SyncDataeotid; @(posedge mdio_mdc) ( current_state ) == ( ACQUIRE ) &&  (  data_counter != 6'h1f ) |-> ( next_state ) == ( ACQUIRE ) ;endproperty 
 property SyncDataeotid; @(posedge mdio_mdc) ( data_counter ) == ( 6'h1f ) &&  (  data_in[31] == 1'b0 && data_in[29:28]==2'b10 && data_in[27:23] == PHY_AD && data_in[22:18] == 5'h11 ) |-> ( speed_select ) == ( data_in_r[16:15] ) &&  (  duplex_mode  == data_in_r[14] ) ;endproperty 
 