property ValidIneotid; @(posedge clk_in_1) (in) |-> (out0 == 1'b1) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 0) && (sel0 == 0)  ) |-> (out0 == 1'b1) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 0) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b1) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 1) && (sel0 == 0)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b1) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 0) && (sel1 == 1) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b1) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 0) && (sel0 == 0)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b1) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 0) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b1) && (out6 == 1'b0) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 1) && (sel0 == 0)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b1) && (out7 == 1'b0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) &&  (  (sel2 == 1) && (sel1 == 1) && (sel0 == 1)  ) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0) && (out4 == 1'b0) && (out5 == 1'b0) && (out6 == 1'b0) && (out7 == 1'b1) ;endproperty 
 