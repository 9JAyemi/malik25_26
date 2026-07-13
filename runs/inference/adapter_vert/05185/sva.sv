property ResetSynceotid; @(posedge clk) (rst) |-> xn == 0 && yn == 0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (rst) != 1'b1 |-> xn == arg_5 && yn == arg_6 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (rst) != 1'b1  &&  (xn != yn) |-> rxy == arg_2 + arg_3 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (rst) != 1'b1  &&  (xn != yn)  |->  r_final == (rxy + 1) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk) (rst) != 1'b1  &&  (xn == yn)  |->  r_final == rxy ;endproperty 
 