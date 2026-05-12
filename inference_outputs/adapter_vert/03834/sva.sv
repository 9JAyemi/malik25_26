property ShiftSynceotid; @(posedge clk_in_15) (A) == (2'b00) |-> (S) == (D) ; endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_15) (A) == (2'b01) |-> (S) == ({D[2:0], 1'b0}) ; endproperty 
 
 property ShiftTwoeotid; @(posedge clk_in_15) (A) == (2'b10) |-> (S) == ({D[1:0], 2'b00}) ; endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_15) (A) == (2'b11) |-> (S) == ({D[0], 3'b000}) ; endproperty 
 