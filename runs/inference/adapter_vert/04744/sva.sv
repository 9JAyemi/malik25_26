property ClockSynceotid; @(posedge clk_in_11) (select) == (2'b00) |-> (out) == (in0) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_11) (select) == (2'b01) |-> (out) == (in1) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_11) (select) == (2'b10) |-> (out) == (in2) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_11) (select) == (2'b11) |-> (out) == (in3) ; endproperty 
 