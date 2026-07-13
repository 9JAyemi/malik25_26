property ClockInveotid; @(posedge clk_in_13) (I) |-> (O) == 1'b0 ; endproperty 
 
 property ANDsynceotid; @(posedge clk_in_13) (A) &&  (B) |-> (Y) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_13) (A) !=  (B)  |-> (Y) == 1'b1 ; endproperty 
 