property LoadSynceotid; @(posedge clk) (load) |-> stage1 == data_in && stage2 == stage1 && stage3 == stage2 && stage4 == stage3 ;endproperty 
 
 property ShiftRighteotid; @(posedge clk) ( !load ) &&  ( shift_right ) |-> stage1 == stage4 && stage2 == stage1 && stage3 == stage2 ;endproperty 
 
 property ShiftIneotid; @(posedge clk) ( !load ) &&  ( !shift_right ) |-> stage1 == stage2 && stage2 == stage3 && stage3 == stage4 ;endproperty 
 
 property DataSynceotid; @(posedge clk) ( !load ) &&  ( !shift_right ) |-> data_out == stage4 ;endproperty 
 