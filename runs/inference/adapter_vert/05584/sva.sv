property ResetSynceotid; @(posedge clk) (rst) |-> count_i == 0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (rst) &&  (  $signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1) ) |-> count_i == 0 ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (rst) && (  $signed({1'b0, count_i}) != ($signed({1'b0, Divisor}) - 1)  ) |->  (count_i == (count_i + 1)) ;endproperty 
 
 property ClockSynceotid; @(posedge clk) (rst)  &&  (  $signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1) )  |->  (clkOut_i == (!clkOut_i)) ;endproperty 
 
 property SyncLockeotid; @(posedge clk) (rst) |-> clkOut  ==  clkOut_i ;endproperty 
 