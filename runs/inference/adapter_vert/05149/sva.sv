property ClockSynceotid; @(posedge clk_in_1) (A) == (B) && (B) == (C) && (C) == (D) |-> (EQ) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (A) != (B) || (C) != (D) |-> (GT) ; endproperty 
 