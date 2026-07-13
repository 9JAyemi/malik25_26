property SyncCheckeotid; @(posedge clk_in_19) (in0) |-> in0_reg == in0 ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_19) (in1) |-> in1_reg == in1 ;endproperty 
 
 property GreaterThaneotid; @(posedge clk_in_19) (in0) > (in1) |-> result == 2'b01 ;endproperty 
 
 property LessThaneotid; @(posedge clk_in_19) (in0) < (in1) |-> result == 2'b10 ;endproperty 
 
 property EqualCheckeotid; @(posedge clk_in_19) (in0) == (in1) |-> result == 2'b00 ;endproperty 
 