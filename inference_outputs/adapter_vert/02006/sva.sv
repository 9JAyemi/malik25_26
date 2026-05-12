property ResetSynceotid; @(posedge clk) (rst) |-> count == 4'b0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |->  (mux_out) == (count[0]) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |->  (count) != 4'b1111 ;endproperty 
 