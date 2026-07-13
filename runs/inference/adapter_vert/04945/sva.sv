property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000000001) |-> (O) == 1'b1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000000010) |-> (O) == 1'b0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000000100) |-> (O) == 1'b1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000001000) |-> (O) == 1'b0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000010000) |-> (O) == 1'b1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000000100000) |-> (O) == 1'b0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000001000000) |-> (O) == 1'b1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000010000000) |-> (O) == 1'b0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b000100000000) |-> (O) == 1'b1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b001000000000) |-> (O) == 1'b0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b010000000000) |-> (O) == 1'b1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) == (12'b100000000000) |-> (O) == 1'b0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (I) != 12'b000000000001 && @(posedge clk_in_1) (I) != 12'b000000000010 && @(posedge clk_in_1) (I) != 12'b000000000100 && @(posedge clk_in_1) (I) != 12'b000000001000 && @(posedge clk_in_1) (I) != 12'b000000010000 && @(posedge clk_in_1) (I) != 12'b000000100000 && @(posedge clk_in_1) (I) != 12'b000001000000 && @(posedge clk_in_1) (I) != 12'b000010000000 && @(posedge clk_in_1) (I) != 12'b000100000000 && @(posedge clk_in_1) (I) != 12'b001000000000 && @(posedge clk_in_1) (I) != 12'b010000000000 && @(posedge clk_in_1) (I) != 12'b100000000000 |-> (O) == 1'b0 ; endproperty 
 