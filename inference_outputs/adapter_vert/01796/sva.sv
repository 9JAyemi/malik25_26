property ResetSynceotid; @(posedge clk) (reset) |-> data_out == 8'b0 && encrypted_data == 8'b0 ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> data_out == encrypted_data ;endproperty 
 
 property ValidDataeotid; @(posedge clk) (reset) != 1'b1 &&  !(enable)  |-> data_out == data_in ;endproperty 
 