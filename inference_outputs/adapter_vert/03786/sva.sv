property SyncEqeotid; @(posedge clk_in_1) ( A ) == (  B ) |-> ( EQ ) == 1'b1 ;endproperty 
 
 property SyncGtNoteThisnameis; @(posedge clk_in_1) ( A ) != (  B ) &&  (  A  -  B  )  |-> ( GT ) == 1'b1 ;endproperty 
 