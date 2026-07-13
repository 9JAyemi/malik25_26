property ClockSynceotid; @(posedge clk_in_1) (A) |-> not_A ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (B) |-> not_B ; endproperty 
 
 property ValidXorOuteotid; @(posedge clk_in_1) (A) &&  ( not_B ) |->  (X) ; endproperty 
 
 property ValidXorOuteotid; @(posedge clk_in_1) (not_A) &&  ( B ) |->  (X) ; endproperty 
 
 