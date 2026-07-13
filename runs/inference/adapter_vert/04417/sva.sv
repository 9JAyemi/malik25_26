property ShiftSynceotid; @(posedge clk_in_15) (shift_amount) == (4'b0000) |-> (result) == (data) ; endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_15) (shift_amount) == (4'b0001) |-> (result) == (data[2:0] & 7'b0000000) ; endproperty 
 
 property ShiftTwoeotid; @(posedge clk_in_15) (shift_amount) == (4'b0010) |-> (result) == (data[1:0] & 7'b0000000) ; endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_15) (shift_amount) == (4'b0011) |-> (result) == (data[0] & 7'b0000000) ; endproperty 
 