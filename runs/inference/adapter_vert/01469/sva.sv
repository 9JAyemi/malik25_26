property ResetSynceotid; @(negedge clk_reset_14) (EN) |-> (Y) == (1'b0) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b00)  ) |-> (Y) == (ABCD) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b01)  ) |-> (Y) == (ABCD) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b10)  ) |-> (Y) == (ABCD) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) (EN) &&  (  (SEL) == (2'b11)  ) |-> (Y) == (ABCD) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_14) ! (EN)  |-> (Y) == (1'bx) ; endproperty 
 