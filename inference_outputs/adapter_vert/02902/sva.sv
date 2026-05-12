property ValidWriteeotid; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt == 2'd3) |-> fifo_wrptr_inc == 4'd3 ;endproperty 
 property ValidWriteeotid; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt != 2'd3) &&  (ge2_free) &&  (input_tm_cnt >= 2'd2) |-> fifo_wrptr_inc == 4'd2 ;endproperty 
 property ValidWriteeotid; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt != 2'd3) &&  (ge2_free) !=  (input_tm_cnt >= 2'd2) &&  (input_tm_cnt >= 2'd1) |-> fifo_wrptr_inc == 4'd1 ;endproperty 
 property ValidWriteeotid; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt != 2'd3) &&  (ge2_free) !=  (input_tm_cnt >= 2'd2) &&  (input_tm_cnt < 2'd1) |-> fifo_wrptr_inc == 4'd0 ;endproperty 
 