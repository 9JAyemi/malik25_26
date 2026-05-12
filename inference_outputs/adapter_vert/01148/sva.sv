property ValidOnRiseeotid; @(posedge clk_in_14) (A_N) && (B) && (C) |-> (X) == 1'b1 ; endproperty 
 
 property SafeStarteotid; @(posedge clk_in_14) (A_N) != 1'b0 &&  (B) != 1'b0 &&  (C) != 1'b0  |-> (X) == 1'b0; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_14) (A_N) != 1'b1 ||  (B) != 1'b1 ||  (C) != 1'b1  |-> (X) == 1'bx; endproperty 
 