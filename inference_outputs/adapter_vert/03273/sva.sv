property BitwiseAndeotid; @(posedge clk_in_1) (operation_select) == (2'b00) |-> result == and_result ; endproperty 
 
 property BitwiseOreotid; @(posedge clk_in_1) (operation_select) == (2'b01) |-> result == or_result ; endproperty 
 
 property BitwiseXorEeotid; @(posedge clk_in_1) (operation_select) == (2'b10) |-> result == xor_result ; endproperty 
 
 property ShiftOnClockeotid; @(posedge clk_in_1) (operation_select) == (2'b11) |-> result == shift_result ; endproperty 
 