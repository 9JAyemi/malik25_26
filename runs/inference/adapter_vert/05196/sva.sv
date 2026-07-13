property ClockSynceotid; @(posedge clk_in_12) (SEL) == (2'b00) |-> (Y) == (D0) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_12) (SEL) == (2'b01) |-> (Y) == (D1) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_12) (SEL) == (2'b10) |-> (Y) == (D2) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_12) (SEL) == (2'b11) |-> (Y) == (D3) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_12) (EN) |-> (Y) == (mux_2to1_out_2) ; endproperty 
 