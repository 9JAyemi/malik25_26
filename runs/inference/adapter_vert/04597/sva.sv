property ClockSynceotid; @(posedge clk_in_1) (sel) |-> (and_0) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (sel) &&  (  ! (in0) &&  (in1)  ) |-> (out) ;endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (sel) &&  (  (in0) &&  ! (in1)  ) |-> (out) ;endproperty 
 