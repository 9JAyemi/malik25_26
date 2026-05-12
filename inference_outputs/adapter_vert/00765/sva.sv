property EnableSynceotid; @(posedge clk_enable_16) (sel) == (2'b00) &&  (enable) |-> (out) == (in0) ;endproperty 
 property EnableSynceotid; @(posedge clk_enable_16) (sel) == (2'b01) &&  (enable) |-> (out) == (in1) ;endproperty 
 property EnableSynceotid; @(posedge clk_enable_16) (sel) == (2'b10) &&  (enable) |-> (out) == (in2) ;endproperty 
 property ValidDataeotid; @(posedge clk_enable_16) (sel) == (2'b11) &&  (enable) |-> (out) == (in3) ;endproperty 
 