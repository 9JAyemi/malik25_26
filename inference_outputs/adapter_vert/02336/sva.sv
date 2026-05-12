property ClockSynceotid; @(posedge clk_in_1) (Sel) == (2'b11) |-> (out) == (S3) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (Sel) != 2'b11 &&  (Sel) == 2'b10  |-> (out) == (S2) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (Sel) != 2'b11 &&  (Sel) != 2'b10  |-> (out) == (S0) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (Sel) == 2'b00  |-> (out) == (S1) ; endproperty 
 