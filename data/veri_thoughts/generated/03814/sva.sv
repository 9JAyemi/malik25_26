module binary_counter_sva
#(parameter n = 4)
(
    input logic rst,
    input logic clk,
    input logic [n-1:0] count
);

    localparam logic [n-1:0] ZERO_COUNT = '0;
    localparam logic [n-1:0] ONE_COUNT  = {{(n-1){1'b0}}, 1'b1};
    localparam logic [n-1:0] MAX_COUNT  = {n{1'b1}};

    // Reset drives the counter to zero on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == ZERO_COUNT)
    );

    // The sampled count matches the RTL next-state function.
    check_state_update_matches_rtl: assert property (
        @(posedge clk) disable iff ($initstate)
        count == ($past(rst) ? ZERO_COUNT :
                 (($past(count) == MAX_COUNT) ? ZERO_COUNT : ($past(count) + ONE_COUNT)))
    );

    // A non-maximum count increments by one on the next non-reset clock.
    check_increment_below_max: assert property (
        @(posedge clk) disable iff (rst)
        (count != MAX_COUNT) |=> (count == ($past(count) + ONE_COUNT))
    );

    // The counter wraps to zero after reaching the maximum value.
    check_wrap_at_max: assert property (
        @(posedge clk) disable iff (rst)
        (count == MAX_COUNT) |=> (count == ZERO_COUNT)
    );

    // Zero advances to one on the next non-reset clock.
    check_zero_advances_to_one: assert property (
        @(posedge clk) disable iff (rst)
        (count == ZERO_COUNT) |=> (count == ONE_COUNT)
    );

    // The count changes on every non-reset clock edge.
    check_count_changes_without_reset: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (count != $past(count))
    );

endmodule