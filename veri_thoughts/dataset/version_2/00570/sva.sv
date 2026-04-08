module fifo_counter_sva (
    input logic clk,
    input logic empty,
    input logic ge2_free,
    input logic ge3_free,
    input logic [1:0] input_tm_cnt,
    input logic [4:0] fifo_cnt_inc
);

    // Output matches the RTL priority function.
    check_full_function: assert property (
        @(posedge clk)
        fifo_cnt_inc == (
            empty ? {3'b000, input_tm_cnt} :
            ((ge3_free && (input_tm_cnt == 2'b11)) ? 5'd2 :
             ((ge2_free && (input_tm_cnt >= 2'd2)) ? 5'd1 :
              ((input_tm_cnt >= 2'd1) ? 5'd0 : 5'b11111)))
        )
    );

    // When empty is high, the output passes through input_tm_cnt.
    check_empty_pass_through: assert property (
        @(posedge clk)
        empty |-> (fifo_cnt_inc == {3'b000, input_tm_cnt})
    );

    // The empty branch has priority over the later branches.
    check_empty_priority: assert property (
        @(posedge clk)
        (empty && ge3_free && ge2_free && (input_tm_cnt == 2'b11)) |-> (fifo_cnt_inc == 5'd3)
    );

    // For non-empty and count 3 with ge3_free, the output is 2.
    check_ge3_free_count3: assert property (
        @(posedge clk)
        (!empty && ge3_free && (input_tm_cnt == 2'b11)) |-> (fifo_cnt_inc == 5'd2)
    );

    // The ge3_free branch overrides ge2_free when both are true.
    check_ge3_priority_over_ge2: assert property (
        @(posedge clk)
        (!empty && ge3_free && ge2_free && (input_tm_cnt == 2'b11)) |-> (fifo_cnt_inc == 5'd2)
    );

    // For non-empty and count 2 with ge2_free, the output is 1.
    check_ge2_free_count2: assert property (
        @(posedge clk)
        (!empty && ge2_free && (input_tm_cnt == 2'b10)) |-> (fifo_cnt_inc == 5'd1)
    );

    // For count 3 without ge3_free but with ge2_free, the output is 1.
    check_count3_ge2_without_ge3: assert property (
        @(posedge clk)
        (!empty && !ge3_free && ge2_free && (input_tm_cnt == 2'b11)) |-> (fifo_cnt_inc == 5'd1)
    );

    // For non-empty and count 1, the output falls through to 0.
    check_count1_maps_zero: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'b01)) |-> (fifo_cnt_inc == 5'd0)
    );

    // For non-empty and count 2 without ge2_free, the output is 0.
    check_count2_without_ge2_maps_zero: assert property (
        @(posedge clk)
        (!empty && !ge2_free && (input_tm_cnt == 2'b10)) |-> (fifo_cnt_inc == 5'd0)
    );

    // For non-empty and count 0, the output is all ones.
    check_count0_maps_all_ones: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'b00)) |-> (fifo_cnt_inc == 5'b11111)
    );

    // The output only takes values produced by the RTL.
    check_output_legal_values: assert property (
        @(posedge clk)
        (fifo_cnt_inc == 5'd0)  ||
        (fifo_cnt_inc == 5'd1)  ||
        (fifo_cnt_inc == 5'd2)  ||
        (fifo_cnt_inc == 5'd3)  ||
        (fifo_cnt_inc == 5'b11111)
    );

endmodule