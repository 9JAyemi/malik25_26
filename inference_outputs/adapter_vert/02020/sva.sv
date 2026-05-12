property AdderSynceotid; @(posedge clk_in_1) (a) |-> (temp_sum) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |-> (sum) == (temp_sum) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) |-> (cout) == (temp_cout) ;endproperty 
 
 property AdderSynceotid; @(posedge clk_in_1) (a) &&  (b) &&  (cin) &&  (  (temp_sum)  != 5'bxxxxx  ) |-> (temp_cout) ;endproperty 
 