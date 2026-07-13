property ValidDataeotid; @(posedge clk_in_1) (sel0) |-> (out[DW-1:0] == in0[DW-1:0]); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (sel1) |-> (out[DW-1:0] == in1[DW-1:0]); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (sel2) |-> (out[DW-1:0] == in2[DW-1:0]); endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) (sel3) |-> (out[DW-1:0] == in3[DW-1:0]); endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (sel0) &&  (  (sel1) ||  (sel2) ||  (sel3)  ) |->  (error)  ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (sel1) &&  (  (sel0) ||  (sel2) ||  (sel3)  ) |->  (error)  ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (sel2) &&  (  (sel0) ||  (sel1) ||  (sel3)  ) |->  (error)  ; endproperty 
 
 property ValidSynceotid; @(posedge clk_in_1) (sel3) &&  (  (sel0) ||  (sel1) ||  (sel2)  ) |->  (error)  ; endproperty 
 