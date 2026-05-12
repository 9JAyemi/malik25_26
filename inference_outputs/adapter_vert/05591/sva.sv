property ShiftIneotid; @(posedge clk_in_1) (dir) |-> (shifted_data_1) == (in << shift) ; endproperty 
 
 property ShiftOuteotid; @(posedge clk_in_1) (dir) &&  (  (shift) != 6'h3  ||  (in) != 16'h0  ||  (shifted_data_1) != 16'h0 )  |-> (shifted_data_2) == (shifted_data_1 << shift) ; endproperty 
 
 property ShiftIneotid; @(posedge clk_in_1) (dir) |-> (out) == (shifted_data_2) ; endproperty 
 