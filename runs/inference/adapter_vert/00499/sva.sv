property ResetSynceotid; @(posedge clk) (reset) |-> register == 4'b0000 ;endproperty 
 
 property LoadSynceotid; @(posedge clk) (reset) |->  (parallel_load) |-> register == parallel_input ;endproperty 
 
 property ShiftLefteotid; @(posedge clk) (reset) |->  ( ! (parallel_load) &&  (shift_left) ) |-> register == {register[2:0], 1'b0} ;endproperty 
 
 property ShiftRighteotid; @(posedge clk) (reset) |->  ( ! (parallel_load)  && !(shift_left) &&  (shift_right) ) |-> register == {1'b0, register[3:1]} ;endproperty 
 