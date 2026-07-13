property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (data) == (x_axis) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b01) |-> (data) == (y_axis) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b10) |-> (data) == (z_axis) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b11) |-> (data) == ({8'h00, temp_data}) ; endproperty 
 