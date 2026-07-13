property ResetSynceotid; @(negedge clk_reset_19) (x) |-> (x_int) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (x) |-> (y_n) == 8'h80 ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (x) &&  (  (y_n1 >= y_n-1 && y_n1 <= y_n+1)  ) |-> (done) == 1'b1 ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (x) &&  (  !(  (y_n1 >= y_n-1 && y_n1 <= y_n+1)  )  ) |-> (y_n) == (y_n1) && (done) == 1'b0 ;endproperty 
 