property ResetSynceotid; @(posedge clk) (rst) |-> shiftreg == 0 && out == 1'b0 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (rst) != 1'b1 && (ld) |-> shiftreg == x && out == 1'b0 ;endproperty 
 
 property ShiftOneotid; @(posedge clk) (rst) != 1'b1 && !(ld)  && (shift) |-> out == shiftreg[0] && shiftreg == {1'b0,shiftreg[63:1]};endproperty 
 