property ClockSynceotid; @(posedge clk_in_1) (sel) == (2'b00) |-> (out) == (in0) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (sel) == (2'b01) |-> (out) == (in1) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (sel) == (2'b10) |-> (out) == (in2) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (sel) == (2'b11) |-> (out) == (in3) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (sel) != 2'b00 && (sel) != 2'b01 && (sel) != 2'b10 && (sel) != 2'b11  |-> (out) == 4'b0 ; endproperty 
 