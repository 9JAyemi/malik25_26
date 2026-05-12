property ResetSynceotid; @(posedge clk) (reset_n) |-> data_out == 0 ;endproperty 
 
 property WriteSynceotid; @(posedge clk) (chipselect) && ( !write_n ) && ( address == 0 ) |-> data_out == writedata ;endproperty 
 
 property ReadSynceotid; @(posedge clk) (chipselect) && ( write_n ) && ( address != 0 ) |-> readdata == data_out ;endproperty 
 