property ResetSynceotid; @(posedge shift_clk) (reset) |-> (q0 == 4'b0000) && (q1 == 4'b0000) && (q2 == 4'b0000) && (q3 == 4'b0000) ;endproperty 
 
 property ShiftSynceotid; @(posedge shift_clk) ( !reset ) |-> (q0 == data_in) && (q1 == q0) && (q2 == q1) && (q3 == q2) ;endproperty 
 