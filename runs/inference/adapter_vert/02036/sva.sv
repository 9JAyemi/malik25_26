property EnableSynceotid; @(posedge clk_enable_19) (EN) |-> (Y) == (A) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (EN) != 1'b1  &&  (A) != (B) |-> (Y) == (B) ; endproperty 
 