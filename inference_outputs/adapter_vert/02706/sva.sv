property GreaterThaneotid; @(posedge clk_in_1) (a) > (b) |-> comparison_result == a && input_selected == 2'b00 ;endproperty 
 
 property GreaterThaneotid; @(posedge clk_in_1) (b) > (a) |-> comparison_result == b && input_selected == 2'b01 ;endproperty 
 
 property Equalizeeotid; @(posedge clk_in_1) (a) == (b)  |-> comparison_result == a && input_selected == select; endproperty 
 