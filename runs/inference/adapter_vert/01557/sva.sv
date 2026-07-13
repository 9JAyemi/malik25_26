property AddSynceotid; @(posedge clk_in_1) (aluc) == (5'd0) |-> result == a + b ; endproperty 
 
 property AddSynceotid; @(posedge clk_in_1) (aluc) == (5'd1) |-> result == a + b ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (aluc) == (5'd2) |-> result == a - b ; endproperty 
 
 property SubSynceotid; @(posedge clk_in_1) (aluc) == (5'd3) |-> result == a - b ; endproperty 
 
 property ANDeotid; @(posedge clk_in_1) (aluc) == (5'd4) |-> result == a & b ; endproperty 
 
 property OReotid; @(posedge clk_in_1) (aluc) == (5'd5) |-> result == a | b ; endproperty 
 
 property XOrEeotid; @(posedge clk_in_1) (aluc) == (5'd6) |-> result == a ^ b ; endproperty 
 
 property ORNOReotid; @(posedge clk_in_1) (aluc) == (5'd7) |-> result == ~(a | b) ; endproperty 
 
 property SetLesseotid; @(posedge clk_in_1) (aluc) == (5'd8) |-> result == (a[31]^b[31])?(a[31]?1:0):(a<b) ; endproperty 
 
 property SetLesseotid; @(posedge clk_in_1) (aluc) == (5'd9) |-> result == a < b ; endproperty 
 
 property ShiftLefteotid; @(posedge clk_in_1) (aluc) == (5'd10) |-> result == b << a ; endproperty 
 
 property ShiftRighteotid; @(posedge clk_in_1) (aluc) == (5'd11) |-> result == b >> a ; endproperty 
 
 property ShiftRightArithmeticeotid; @(posedge clk_in_1) (aluc) == (5'd12) |-> result == $signed(b) >>> a ; endproperty 
 
 property LoadUpeotid; @(posedge clk_in_1) (aluc) == (5'd14) |-> result == {b[15:0], 16'b0} ; endproperty 
 
 property Zeroeotid; @(posedge clk_in_1) (aluc) == (5'd31) |-> result == 0 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (aluc) != 5'd0 && @(posedge clk_in_1) (aluc) != 5'd1 && @(posedge clk_in_1) (aluc) != 5'd2 && @(posedge clk_in_1) (aluc) != 5'd3 && @(posedge clk_in_1) (aluc) != 5'd4 && @(posedge clk_in_1) (aluc) != 5'd5 && @(posedge clk_in_1) (aluc) != 5'd6 && @(posedge clk_in_1) (aluc) != 5'd7 && @(posedge clk_in_1) (aluc) != 5'd8 && @(posedge clk_in_1) (aluc) != 5'd9 && @(posedge clk_in_1) (aluc) != 5'd10 && @(posedge clk_in_1) (aluc) != 5'd11 && @(posedge clk_in_1) (aluc) != 5'd12 && @(posedge clk_in_1) (aluc) != 5'd14 && @(posedge clk_in_1) (aluc) != 5'd31  |-> result == 0; endproperty 
 