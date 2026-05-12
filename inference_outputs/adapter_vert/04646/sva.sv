property AddSynceotid; @(posedge clk_in_1) (op) == (2'b00) |-> add_out == a + b && sub_out == 0 && mul_out == 0 && div_out == 0 ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (op) == (2'b01) |-> add_out == 0 && sub_out == a - b && mul_out == 0 && div_out == 0 ; endproperty 
 
 property MultSynceotid; @(posedge clk_in_1) (op) == (2'b10) |-> add_out == 0 && sub_out == 0 && mul_out == a * b && div_out == 0 ; endproperty 
 
 property DivSynceotid; @(posedge clk_in_1) (op) == (2'b11) |-> add_out == 0 && sub_out == 0 && mul_out == 0 && div_out == a / b ; endproperty 
 