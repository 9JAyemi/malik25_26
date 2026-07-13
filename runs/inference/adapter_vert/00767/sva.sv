property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000000) |-> (td_mode) == 4'b0000 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000001) |-> (td_mode) == 4'b1000 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000010) |-> (td_mode) == 4'b0100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000011) |-> (td_mode) == 4'b1100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000100) |-> (td_mode) == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000101) |-> (td_mode) == 4'b1010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000110) |-> (td_mode) == 4'b0101 ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000111) |-> (td_mode) == 4'b1111 ; endproperty 
 
 property SyncCtrleotid; (ctrl) != 7'b0000000 && (ctrl) != 7'b0000001 && (ctrl) != 7'b0000010 && (ctrl) != 7'b0000011 && (ctrl) != 7'b0000100 && (ctrl) != 7'b0000101 && (ctrl) != 7'b0000110 && (ctrl) != 7'b0000111  |-> (td_mode) == 4'b0000; endproperty 
 