property ValidDataeotid; @(posedge clk_gen_19) (din0) |-> (tmp_mul) ;endproperty 
 
 property ValidAccumulateeotid; @(posedge clk_gen_19) (din0) &&  (din1) &&  (din2) |-> (acc_result) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_gen_19) (din0) &&  (din1) &&  (din2) |-> (dout) ;endproperty 
 