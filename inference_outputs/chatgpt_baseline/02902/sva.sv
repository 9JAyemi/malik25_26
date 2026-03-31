module fifo_controller_sva (
    input logic clk,
    input logic ge2_free,
    input logic ge3_free,
    input logic [1:0] input_tm_cnt,
    input logic [3:0] fifo_wrptr_inc
);
    // Output matches the RTL's piecewise function for all input combinations.
    check_functional_spec: assert property (
        @(posedge clk)
        fifo_wrptr_inc == ( (ge3_free && (input_tm_cnt == 2'd3)) ? 4'd3 :
                            (ge2_free && (input_tm_cnt >= 2'd2)) ? 4'd2 :
                            (input_tm_cnt >= 2'd1)               ? 4'd1 :
                                                                     4'd0 )
    );

    // Output is always in the set {0,1,2,3}.
    check_output_range: assert property (
        @(posedge clk) fifo_wrptr_inc inside {4'd0, 4'd1, 4'd2, 4'd3}
    );

    // When input_tm_cnt is 0, increment is 0.
    check_tm_cnt0_zero: assert property (
        @(posedge clk) (input_tm_cnt == 2'd0) |-> (fifo_wrptr_inc == 4'd0)
    );

    // When input_tm_cnt is 1, increment is 1 (independent of ge2_free/ge3_free).
    check_tm_cnt1_one: assert property (
        @(posedge clk) (input_tm_cnt == 2'd1) |-> (fifo_wrptr_inc == 4'd1)
    );

    // When input_tm_cnt is 2 and ge2_free is true, increment is 2.
    check_tm_cnt2_ge2_true: assert property (
        @(posedge clk) (input_tm_cnt == 2'd2) && ge2_free |-> (fifo_wrptr_inc == 4'd2)
    );

    // When input_tm_cnt is 2 and ge2_free is false, increment is 1.
    check_tm_cnt2_ge2_false: assert property (
        @(posedge clk) (input_tm_cnt == 2'd2) && !ge2_free |-> (fifo_wrptr_inc == 4'd1)
    );

    // When input_tm_cnt is 3 and ge3_free is true, increment is 3 (highest priority).
    check_tm_cnt3_ge3_true: assert property (
        @(posedge clk) (input_tm_cnt == 2'd3) && ge3_free |-> (fifo_wrptr_inc == 4'd3)
    );

    // When input_tm_cnt is 3, ge3_free is false, and ge2_free is true, increment is 2.
    check_tm_cnt3_ge2_only_yields_two: assert property (
        @(posedge clk) (input_tm_cnt == 2'd3) && !ge3_free && ge2_free |-> (fifo_wrptr_inc == 4'd2)
    );

    // When input_tm_cnt is 3 and both ge3_free and ge2_free are false, increment is 1.
    check_tm_cnt3_no_free_yields_one: assert property (
        @(posedge clk) (input_tm_cnt == 2'd3) && !ge3_free && !ge2_free |-> (fifo_wrptr_inc == 4'd1)
    );
endmodule