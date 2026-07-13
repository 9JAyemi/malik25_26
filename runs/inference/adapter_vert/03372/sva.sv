property ClockSynceotid; @(posedge clk_in_13) (sel) == (4'b0000) |-> (out) == (in) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_13) (sel) == (4'b0001) |-> (out) == (in) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_13) (sel) == (4'b0010) |-> (out) == (in) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_13) (sel) == (4'b0011) |-> (out) == (in) ; endproperty 
 
 property ValidDataeotid; @(posedge clk_in_13) (sel) != 4'b0000 && @(posedge clk_in_13) (sel) != 4'b0001 && @(posedge clk_in_13) (sel) != 4'b0010 && @(posedge clk_in_13) (sel) != 4'b0011  |-> (out) == 6'b000000; endproperty 
 