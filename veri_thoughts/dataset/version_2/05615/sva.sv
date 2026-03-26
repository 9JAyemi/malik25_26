module counter_sva (
    input logic clk,
    input logic start,
    input logic [2:0] count
);

    // Count increments by one when start is high below seven.
    check_count_increments: assert property (
        @(posedge clk) (start && (count != 3'd7)) |=> (count == ($past(count) + 3'd1))
    );

    // Count wraps to zero when start is high at seven.
    check_count_wraps_at_seven: assert property (
        @(posedge clk) (start && (count == 3'd7)) |=> (count == 3'd0)
    );

    // Count holds its value when start is low.
    check_count_holds_when_start_low: assert property (
        @(posedge clk) (!start) |=> (count == $past(count))
    );

    // Next-state behavior always matches the RTL update rule.
    check_count_next_state_rule: assert property (
        @(posedge clk) 1'b1 |=> (
            count == ($past(start) ? (($past(count) == 3'd7) ? 3'd0 : ($past(count) + 3'd1)) : $past(count))
        )
    );

endmodule