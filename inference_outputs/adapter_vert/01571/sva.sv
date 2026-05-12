property ResetSynceotid; @(posedge clk) (reset) |-> reg_0x1F == 8'h00 ;endproperty 
 
 property WriteSynceotid; @(posedge clk) ( !reset ) &&  (  wenb ) |-> reg_0x1F == reg_0x1F ;endproperty 
 
 property WriteSynceotid; @(posedge clk) ( !reset ) &&  (  !wenb ) |-> reg_0x1F == in_data ;endproperty 
 