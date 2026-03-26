module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // The next count follows the RTL reset, rollover, and increment logic.
    check_next_state_function: assert property (
        @(posedge clk) disable iff ($initstate)
        1'b1 |=> (count == ($past(reset) ? 4'd0 :
                            (($past(count) == 4'd9) ? 4'd0 : ($past(count) + 4'd1))))
    );

    // Active-high synchronous reset drives count to zero on the next cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (count == 4'd0)
    );

    // A count of 9 rolls over to 0 when reset is low.
    check_rollover_from_nine: assert property (
        @(posedge clk) disable iff ($initstate)
        (!reset && (count == 4'd9)) |=> (count == 4'd0)
    );

    // Any non-9 count increments by 1 when reset is low.
    check_increment_when_not_nine: assert property (
        @(posedge clk) disable iff ($initstate)
        (!reset && (count != 4'd9)) |=> (count == ($past(count) + 4'd1))
    );

    // Once in the 0 to 9 sequence, the next count stays in that range.
    check_valid_range_preserved: assert property (
        @(posedge clk) disable iff ($initstate)
        (!reset && (count <= 4'd9)) |=> (count <= 4'd9)
    );

endmodule