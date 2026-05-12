property ResetSynceotid; @(negedge nrst_i) ( nrst_i ) |-> ( adr ) == ( 23'b1111_1111_1111_1111_1111_111 ) && ( cmd ) == ( 3'b111 ) && ( idsel_s ) == ( 1'b0 ) ;endproperty 
 
 property SyncLoadeotid; @(negedge nrst_i) ( nrst_i ) &&  (  pciadrLD_i == 1 ) |-> ( adr ) == ( ad_i ) && ( cmd ) == ( cbe_i ) && ( idsel_s ) == ( idsel_i ) ;endproperty 
 
 property ValidAccesseotid; @(negedge nrst_i) ( memEN_i == 1'b1 ) &&  (  adr [31:25] == bar0_i ) &&  (  adr [1:0] == 2'b00 ) &&  (  cmd [3:1] == 3'b011 )  |-> ( adrmem_o ) == ( 1'b1 ) ;endproperty 
 
 property ValidAccesseotid; @(negedge nrst_i) ( idsel_s == 1'b1 ) &&  (  adr [1:0] == 2'b00 ) &&  (  cmd [3:1] == 3'b101 )  |-> ( adrcfg_o ) == ( 1'b1 ) ;endproperty 
 
 property ValidDataeotid; @(negedge nrst_i) (  cbe_i [3] && cbe_i [2] ) |-> ( a1 ) == ( 1'b0 ) ;endproperty 
 
 property ValidDataeotid; @(negedge nrst_i) (  cbe_i [3] && cbe_i [2] ) |-> ( adr_o ) == ( {adr [24:2], a1} ) ;endproperty 
 
 property ValidCmdseotid; @(negedge nrst_i) (  cbe_i [3] && cbe_i [2] ) |-> ( cmd_o ) == ( cmd ) ;endproperty 
 