module fifo_controller_sva (
    input logic clk,
    input logic ge2_free,
    input logic ge3_free,
    input logic [1:0] input_tm_cnt,
    input logic [3:0] fifo_wrptr_inc
);

// ge3_free and input_tm_cnt==3 select 3.
    check_ge3_selects_3: assert property (
        @(posedge clk) (ge3_free && (input_tm_cnt == 2'd3)) |-> (fifo_wrptr_inc == 4'd3)
    );

// When ge3_free and input_tm_cnt==3, ge2_free has no effect.
    check_ge3_overrides_ge2: assert property (
        @(posedge clk) (ge3_free && (input_tm_cnt == 2'd3) && ge2_free) |-> (fifo_wrptr_inc == 4'd3)
    );

// ge2_free and input_tm_cnt>=2 select 2.
    check_ge2_selects_2: assert property (
        @(posedge clk) (ge2_free && (input_tm_cnt >= 2'd2)) |-> (fifo_wrptr_inc == 4'd2)
    );

// When ge2_free and input_tm_cnt>=2, input_tm_cnt==1 selects 1.
    check_ge2_overrides_tm1: assert property (
        @(posedge clk) (ge2_free && (input_tm_cnt >= 2'd2) && (input_tm_cnt == 2'd1)) |-> (fifo_wrptr_inc == 4'd1)
    );

// input_tm_cnt>=1 selects 1 when neither ge2_free nor ge3_free is asserted.
    check_tm1_selects_1_without_ge: assert property (
        @(posedge clk) ((input_tm_cnt >= 2'd1) && !ge2_free && !ge3_free) |-> (fifo_wrptr_inc == 4'd1)
    );

// input_tm_cnt==0 selects 0 when neither ge2_free nor ge3_free is asserted.
    check_tm0_selects_0_without_ge: assert property (
        @(posedge clk) ((input_tm_cnt == 2'd0) && !ge2_free && !ge3_free) |-> (fifo_wrptr_inc == 4'd0)
    );

// When neither ge2_free nor ge3_free is asserted, output is 0 or 1.
    check_without_ge_is_0_or_1: assert property (
        @(posedge clk) (!ge2_free && !ge3_free) |-> (fifo_wrptr_inc == 4'd0 || fifo_wrptr_inc == 4'd1)
    );

// When ge2_free is asserted, output is 0, 1, or 2.
    check_ge2_bounds: assert property (
        @(posedge clk) ge2_free |-> (fifo_wrptr_inc == 4'd0 || fifo_wrptr_inc == 4'd1 || fifo_wrptr_inc == 4'd2)
    );

// When ge3_free is asserted, output is 0, 1, 2, or 3.
    check_ge3_bounds: assert property (
        @(posedge clk) ge3_free |-> (fifo_wrptr_inc == 4'd0 || fifo_wrptr_inc == 4'd1 || fifo_wrptr_inc == 4'd2 || fifo_wrptr_inc == 4'd3)
    );

endmodule
