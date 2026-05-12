property ResetSynceotid; @(posedge clk) (rst_n) |-> count == 16'b0000000000000000 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst_n) &&  (  clk  !=  rst_18  || clk_16  != rx_18 ) |->  clk_15 ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst_n) |->  clk_15 ;endproperty 
 