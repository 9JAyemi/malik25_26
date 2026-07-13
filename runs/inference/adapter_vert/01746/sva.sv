property ValidCoinForItemeotid; @(posedge clk_in_1) (item) == (2'b00) |-> (vend) == 0 ; endproperty 
 
 property ValidCoinForItemAeotid; @(posedge clk_in_1) (item) == (2'b01) &&  (coin >= 2'b01) &&  (dispense) |-> (vend) == 1 ; endproperty 
 
 property ValidCoinForItemBeotid; @(posedge clk_in_1) (item) == (2'b10) &&  (coin >= 2'b10) &&  (dispense) |-> (vend) == 1 ; endproperty 
 
 property ValidCoinForItemCeotid; @(posedge clk_in_1) (item) == (2'b11) &&  (coin >= 2'b11) &&  (dispense) |-> (vend) == 1 ; endproperty 
 