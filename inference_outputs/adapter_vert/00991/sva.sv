property ShiftSynceotid; @(posedge clk_in_15) (shift_amount) == (2'b00) |-> data_out == data_in ; endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_15) (shift_amount) == (2'b01) |-> data_out == data_in ; endproperty 
 
 property ShiftTwoeotid; @(posedge clk_in_15) (shift_amount) == (2'b10) |-> data_out == data_in ; endproperty 
 
 property ShiftSynceotid; @(posedge clk_in_15) (shift_amount) != 2'b00 && (shift_amount) != 2'b01 && (shift_amount) != 2'b10  |-> data_out == data_in ; endproperty 
 