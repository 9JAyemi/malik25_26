property SafeStarteotid; @(posedge clk_enable_19) (A) |-> (nand1_out) ;endproperty 
 
 property SafeStarteotid; @(posedge clk_enable_19) (A) &&  (B) &&  (EN) |-> (nand2_out) ;endproperty 
 
 property ValidInputeotid; @(posedge clk_enable_19) (A) &&  (B) &&  (EN) |-> (and_out) ;endproperty 
 
 property ValidSynceotid; @(posedge clk_enable_19) (A) &&  (B) &&  (EN) &&  (nand2_out) &&  (and_out) |-> (Z) ;endproperty 
 