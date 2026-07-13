property ShiftLefteotid; @(posedge clk_in_1) (shift_left) |-> (out) == (in << shift_amt) ; endproperty 
 
 property ShiftRighteotid; @(posedge clk_in_1) (shift_left) != 1'b1  |-> (out) == (in >> shift_amt) ; endproperty 
 