property ClockSynceotid; @(posedge clk_in_17) (binary_input) |-> (gray_code_output) ;endproperty 
 
 property ShiftSynceotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) == (2'b00)  ) |-> (shifted_gray_code_output) == (data) ;endproperty 
 
 property ShiftOneotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) == (2'b01)  ) |-> (shifted_gray_code_output) == ({data[2:0], data[3]}) ;endproperty 
 
 property ShiftTwoeotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) == (2'b10)  ) |-> (shifted_gray_code_output) == ({data[1:0], data[3:2]}) ;endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_17) (gray_code_output) &&  (  (shift_amount) != 2'b00 &&  (shift_amount) != 2'b01 &&  (shift_amount) != 2'b10  ) |-> (shifted_gray_code_output) == ({data[0], data[3:1]}) ;endproperty 
 