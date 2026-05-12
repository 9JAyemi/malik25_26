property ClockSynceotid; @(posedge clk_in_1) (in) == (2'b00) |-> (out0) == 1 && (out1) == 0 && (out2) == 0 && (out3) == 0 ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) == (2'b01) |-> (out0) == 0 && (out1) == 1 && (out2) == 0 && (out3) == 0 ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) == (2'b10) |-> (out0) == 0 && (out1) == 0 && (out2) == 1 && (out3) == 0 ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) == (2'b11) |-> (out0) == 0 && (out1) == 0 && (out2) == 0 && (out3) == 1 ; endproperty 
 