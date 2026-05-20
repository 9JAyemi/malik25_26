module fifo_controller_sva (
    input logic fifo_wrptr_inc,
    input logic ge2_free,
    input logic ge3_free,
    input logic input_tm_cnt,
    input logic clk_in_17,
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3
);

property ValidWriteeotid; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt == 2'd3) |-> fifo_wrptr_inc == 4'd3 ;endproperty
assert property (ValidWriteeotid);

property ValidWriteeotid_2; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt != 2'd3) &&  (ge2_free) &&  (input_tm_cnt >= 2'd2) |-> fifo_wrptr_inc == 4'd2 ;endproperty
assert property (ValidWriteeotid_2);

property ValidWriteeotid_3; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt != 2'd3) &&  (ge2_free) !=  (input_tm_cnt >= 2'd2) &&  (input_tm_cnt >= 2'd1) |-> fifo_wrptr_inc == 4'd1 ;endproperty
assert property (ValidWriteeotid_3);

property ValidWriteeotid_4; @(posedge clk_in_17) (ge3_free) &&  (input_tm_cnt != 2'd3) &&  (ge2_free) !=  (input_tm_cnt >= 2'd2) &&  (input_tm_cnt < 2'd1) |-> fifo_wrptr_inc == 4'd0 ;endproperty
assert property (ValidWriteeotid_4);

endmodule