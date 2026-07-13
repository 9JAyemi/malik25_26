property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd0) |-> (bin_out) == 8'b00000000 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd1) |-> (bin_out) == 8'b00000001 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd2) |-> (bin_out) == 8'b00000010 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd3) |-> (bin_out) == 8'b00000011 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd4) |-> (bin_out) == 8'b00000100 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd5) |-> (bin_out) == 8'b00000101 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd6) |-> (bin_out) == 8'b00000110 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd7) |-> (bin_out) == 8'b00000111 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd8) |-> (bin_out) == 8'b00001000 ; endproperty 
 
 property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd9) |-> (bin_out) == 8'b00001001 ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (bcd_in) != 4'b1111 |-> (bin_out) != 8'b11111111 ; endproperty 
 