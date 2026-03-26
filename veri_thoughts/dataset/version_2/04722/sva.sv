module fifo_counter_assertions (
    input logic clk,
    input logic empty,
    input logic ge2_free,
    input logic ge3_free,
    input logic [1:0] input_tm_cnt,
    input logic [4:0] fifo_cnt_inc
);

    // Empty passes the input count through with zero extension.
    check_empty_pass_through: assert property (
        @(posedge clk)
        empty |-> (fifo_cnt_inc == {3'b000, input_tm_cnt})
    );

    // Non-empty with zero input count returns 31.
    check_nonempty_count0_returns_31: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd0)) |-> (fifo_cnt_inc == 5'd31)
    );

    // Non-empty with input count 1 returns 0.
    check_nonempty_count1_returns_0: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd1)) |-> (fifo_cnt_inc == 5'd0)
    );

    // Non-empty with input count 2 and ge2_free set returns 1.
    check_nonempty_count2_ge2_returns_1: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd2) && ge2_free) |-> (fifo_cnt_inc == 5'd1)
    );

    // Non-empty with input count 2 and ge2_free clear returns 0.
    check_nonempty_count2_no_ge2_returns_0: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd2) && !ge2_free) |-> (fifo_cnt_inc == 5'd0)
    );

    // Non-empty with input count 3 and ge3_free set returns 2.
    check_nonempty_count3_ge3_returns_2: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd3) && ge3_free) |-> (fifo_cnt_inc == 5'd2)
    );

    // Non-empty with input count 3 uses the ge2_free case when ge3_free is clear.
    check_nonempty_count3_ge2_only_returns_1: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd3) && !ge3_free && ge2_free) |-> (fifo_cnt_inc == 5'd1)
    );

    // Non-empty with input count 3 returns 0 when neither free threshold applies.
    check_nonempty_count3_no_free_threshold_returns_0: assert property (
        @(posedge clk)
        (!empty && (input_tm_cnt == 2'd3) && !ge3_free && !ge2_free) |-> (fifo_cnt_inc == 5'd0)
    );

endmodule