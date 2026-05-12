property EnableSynceotid; @(posedge clk_enable_14) (EN) |-> (Y) == (4'b0001) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) (EN) &&  (  {A,B} == 2'b01  ) |-> (Y) == (4'b0010) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) (EN) &&  (  {A,B} == 2'b10  ) |-> (Y) == (4'b0100) ; endproperty 
 
 property ValidOnEnableeotid; @(posedge clk_enable_14) (EN) &&  (  {A,B} == 2'b11  ) |-> (Y) == (4'b1000) ; endproperty 
 
 property EnableSynceotid; @(posedge clk_enable_14) ! (EN)  |-> (Y) == (4'b0000) ; endproperty 
 