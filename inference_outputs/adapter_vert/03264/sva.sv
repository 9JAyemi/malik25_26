property ResetSynceotid; @(posedge clk) (clear) |-> count_out == 4'b0 ; endproperty 
 
 property LoadSynceotid; @(posedge clk) (clear) &&  (load) |-> count_out == data_in ; endproperty 
 
 property UpSynceotid; @(posedge clk) (clear) &&  (load) != 1  &&  (up_down) |-> count_out == count_out + 4'b1 ; endproperty 
 
 property DownSynceotid; @(posedge clk) (clear) &&  (load) != 1  &&  (up_down) != 1  |-> count_out == count_out - 4'b1 ; endproperty 
 