module mux_counter_sva (
    input logic        clk,
    input logic [7:0]  data_in1,
    input logic [7:0]  data_in2,
    input logic        select,
    input logic        reset,
    input logic [7:0]  sum_out,
    input logic [3:0]  count,
    input logic [7:0]  output1,
    input logic [7:0]  output2
);

    // State registers are cleared after a reset cycle.
    check_state_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (count == 4'b0000 && output1 == 8'b00000000 && output2 == 8'b00000000)
    );

    // sum_out is zero once the cleared state from reset is visible.
    check_sum_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (sum_out == 8'b00000000)
    );

    // count increments by one on each non-reset cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (count == ($past(count) + 4'b0001))
    );

    // output1 captures data_in1 on each non-reset cycle.
    check_output1_captures_data_in1: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (output1 == $past(data_in1))
    );

    // output2 captures data_in2 on each non-reset cycle.
    check_output2_captures_data_in2: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (output2 == $past(data_in2))
    );

    // When select is low, sum_out uses output1 plus twice count.
    check_sum_uses_output1_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |-> (sum_out == (output1 + {count, 1'b0}))
    );

    // When select is high, sum_out uses output2 plus twice count.
    check_sum_uses_output2_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (sum_out == (output2 + {count, 1'b0}))
    );

endmodule