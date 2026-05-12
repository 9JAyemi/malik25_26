property EnableSynceotid; @(posedge clk_enable_13) (sel) == (2'b00) &&  (en) |-> (out) == (in0) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_13) (sel) == (2'b01) &&  (en) |-> (out) == (in1) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_13) (sel) == (2'b10) &&  (en) |-> (out) == (in2) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_13) (sel) == (2'b11) &&  (en) |-> (out) == (in3) ; endproperty 
 
 property ValidIneotid; @(posedge clk_enable_13) (sel) != 2'b00 && @(posedge clk_enable_13) (sel) != 2'b01 && @(posedge clk_enable_13) (sel) != 2'b10 && @(posedge clk_enable_13) (sel) != 2'b11  |-> (out) == 4'b0 ; endproperty 
 