property ClockSynceotid; @(posedge clk_osc_19) (A1) |-> (temp1) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_19) (A1) != (B1) |-> (temp2) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_19) (B1) != 1'b1  |-> (temp3) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_19) (A1)  |-> (temp4) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_osc_19) (A1) |-> (X) == (temp1 & temp2 | temp3 & temp4) ; endproperty 
 