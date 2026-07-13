property ClockSynceotid; @(posedge clk) (q) |-> (q_reg == q + 1) ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (q) &&  (  q_reg == 4'b1111 ) |-> (q_reg == 4'b0000) ; endproperty 
 
 property ClockSynceotid; @(posedge osc_clk) (led) |-> (c_delay == 23'h000000) ; endproperty 
 
 property ClockSynceotid; @(posedge osc_clk) (led) &&  (  !rstn ) |-> (c_delay == 23'h000000) ; endproperty 
 
 property ClockSynceotid; @(posedge osc_clk) (led) &&  (  rstn ) |-> (c_delay == c_delay + 1) ; endproperty 
 
 property ClockSynceotid; @(posedge osc_clk) (clk) |-> (c_delay == 23'h000000) ; endproperty 
 
 property ClockSynceotid; @(posedge osc_clk) (clk) &&  (  !rstn ) |-> (c_delay == 23'h000000) ; endproperty 
 
 property ClockSynceotid; @(posedge osc_clk) (clk) &&  (  rstn ) |-> (c_delay == c_delay + 1) ; endproperty 
 