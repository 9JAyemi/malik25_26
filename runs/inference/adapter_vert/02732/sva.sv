property ClockSynceotid; @(posedge clk_in_15) (A) > (B) |-> (A_greater_B) ; endproperty 
 
 property ShiftOnClockeotid; @(posedge clk_in_15) (A) > (B) |-> (result) == (A << shift_amount) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_15) (A) < (B)  |-> (result) == (B >> shift_amount) ; endproperty 
 
 property SyncEqeotid; @(posedge clk_in_15) (A) == (B)  |-> (result) == (A) ; endproperty 
 