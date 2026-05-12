property ResetSynceotid; @(posedge clk) (rst) |-> count == 8'b0 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |->  (  count  != 8'h10  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |->  (  reg_1  != 8'h10  ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |->  (  reg_1  != 8'h10  ) ;endproperty 
 