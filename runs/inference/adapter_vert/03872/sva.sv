property EnableSynceotid; @(posedge clk_enable_14) (SEL) == (2'b00) |-> (Y) == (D0) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) (SEL) == (2'b01) |-> (Y) == (D1) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) (SEL) == (2'b10) |-> (Y) == (D2) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) (SEL) == (2'b11) |-> (Y) == (D3) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) (EN) != 1'b1  |-> (Y) == 8'b0 ; endproperty 
 