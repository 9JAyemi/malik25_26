property ShiftLefteotid; @(posedge clk_in_11) (SHIFT_DIRECTION) == (0) |-> (SHIFTED_DATA) == (DATA << SHIFT_AMOUNT) ; endproperty 
 
 property ShiftRighteotid; @(posedge clk_in_11) (SHIFT_DIRECTION) != 0 |-> (SHIFTED_DATA) == (DATA >> SHIFT_AMOUNT) ; endproperty 
 