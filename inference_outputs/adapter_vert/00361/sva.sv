property EnableSynceotid; @(posedge clk_enable_19) (EN) |-> (Q) == (D) ;endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (EN) &&  (TE) |-> (Q) == (D) ;endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (EN) &&  (TE) |-> (ENCLK) == (1'b1) ;endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_19) (EN) &&  ( !  TE ) |-> (ENCLK) == (1'b0) ;endproperty 
 