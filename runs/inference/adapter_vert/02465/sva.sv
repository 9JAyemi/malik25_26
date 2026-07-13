property ClockSynceotid; @(posedge clk_in_1) (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1) |-> X == 1'b1 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1) && (  (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)  != 1'b1  ) |-> X == 1'b0 ;endproperty 
 