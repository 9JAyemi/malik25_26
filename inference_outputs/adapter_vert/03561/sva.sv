property ClockSynceotid; @(posedge clk_in) (count) == (n - 1) |-> clk_out == ~clk_out ;endproperty 
 
 property ClockSynceotid; @(posedge clk_in) (count) != (n - 1) |-> clk_out == clk_out ;endproperty 
 