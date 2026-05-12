property LoadSynceotid; @(posedge clk) (load) |-> data_out == data_in ; endproperty 
 
 property ShiftOneotid; @(posedge clk) ( !load )  |-> data_out == data_out ; endproperty 
 