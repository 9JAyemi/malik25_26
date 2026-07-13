property ClockSynceotid; @(posedge clk_in_1) (S) == (2'b00) |-> (Y) == (C) ; endproperty 
 
 property DataSynceotid; @(posedge clk_in_1) (S) == (2'b01) |-> (Y) == (D) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (S) == (2'b10) |-> (Y) == (A) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (S) == (2'b11) |-> (Y) == (B) ; endproperty 
 