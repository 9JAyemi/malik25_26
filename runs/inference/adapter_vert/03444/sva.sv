property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (2'b00) |-> (S) == (D0) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (2'b01) |-> (S) == (D1) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (2'b10) |-> (S) == (D2) ; endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (2'b11) |-> (S) == (D3) ; endproperty 
 
 property ValidCtrleotid; @(posedge clk_in_14) (ctrl) != 2'b00 && (ctrl) != 2'b01 && (ctrl) != 2'b10 && (ctrl) != 2'b11 |-> (S) == 1'bx ; endproperty 
 