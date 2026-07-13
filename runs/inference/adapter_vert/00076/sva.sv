property ShiftSynceotid; @(posedge clk_in_1) (shift_dir) |-> (shift_amount == 2'b00) && (A == shifted_A); endproperty 
 
 property ShiftOneeotid; @(posedge clk_in_1) (shift_dir) && (shift_amount == 2'b01) |-> (shifted_A == {A[2:0], 1'b0}); endproperty 
 
 property ShiftTwoeotid; @(posedge clk_in_1) (shift_dir) && (shift_amount == 2'b10) |-> (shifted_A == {A[1:0], 2'b00}); endproperty 
 
 property ShiftThreeseotid; @(posedge clk_in_1) (shift_dir) && (shift_amount != 2'b00) && (shift_amount != 2'b01) && (shift_amount != 2'b10) |-> (shifted_A == {A[0], 3'b000}); endproperty 
 
 property EnableSynceotid; @(posedge clk_in_1) (enable) && (select == 2'b00) |-> (out == 16'h0001); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (enable) && (select == 2'b01) |-> (out == 16'h0002); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (enable) && (select == 2'b10) |-> (out == 16'h0004); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (enable) && (select == 2'b11) |-> (out == 16'h0008); endproperty 
 
 property SafeSynceotid; @(posedge clk_in_1) ! (enable)  |-> (out == 16'b0); endproperty 
 