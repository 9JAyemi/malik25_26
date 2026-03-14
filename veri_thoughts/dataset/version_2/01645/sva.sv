module top_module_sva (
    input logic clk,
    input logic reset,
    input logic load,
    input logic up_down,
    input logic [3:0] data_in,
    input logic [7:0] data_out,
    input logic [7:0] count1,   // top_module internal
    input logic [7:0] count2,   // top_module internal
    input logic [7:0] sum       // top_module internal
);

    ///// up_counter_with_reset_and_load /////
    // Synchronous reset drives count1 to 0.
    check_count1_resets_to_zero: assert property (
        @(posedge clk) reset |-> (count1 == 8'd0)
    );
    // load drives count1 to 0 when not in reset.
    check_count1_load_clears: assert property (
        @(posedge clk) disable iff (reset) load |-> (count1 == 8'd0)
    );
    // When neither reset nor load, count1 increments by 1 each cycle.
    check_count1_inc_when_no_reset_load: assert property (
        @(posedge clk) disable iff (reset) (!load) |-> (count1 == $past(count1) + 8'd1)
    );

    ///// up_down_counter_with_load /////
    // load drives count2 to 0.
    check_count2_load_clears: assert property (
        @(posedge clk) disable iff (reset) load |-> (count2 == 8'd0)
    );
    // When !load and up_down=1, count2 increments by 1.
    check_count2_inc_when_up_no_load: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |-> (count2 == $past(count2) + 8'd1)
    );
    // When !load and up_down=0, count2 decrements by 1.
    check_count2_dec_when_down_no_load: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |-> (count2 == $past(count2) - 8'd1)
    );

    ///// summing_module and top-level wiring /////
    // sum equals truncated 8-bit addition of count1 and count2.
    check_sum_matches_truncated_add: assert property (
        @(posedge clk) disable iff (reset) sum == ((count1 + count2) & 9'h0FF)
    );
    // data_out is driven by sum.
    check_data_out_eq_sum: assert property (
        @(posedge clk) disable iff (reset) data_out == sum
    );
    // When !reset, !load, and up_down=1, sum advances by +2 modulo 256.
    check_sum_advances_by_two_on_up: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down) |-> (sum == (($past(sum) + 8'd2) & 9'h0FF))
    );
    // When !reset, !load, and up_down=0, sum is unchanged.
    check_sum_stable_on_down: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down) |-> (sum == $past(sum))
    );

endmodule