module UpCounter_sva #(
    parameter int Size = 8
)(
    input logic             clock,
    input logic             reset,
    input logic             count,
    input logic [Size-1:0]  data_o
);

    // Reset clears the counter output to zero.
    check_reset_clears_data: assert property (
        @(posedge clock) reset |=> (data_o == {Size{1'b0}})
    );

    // Reset has priority over count when both are high.
    check_reset_priority_over_count: assert property (
        @(posedge clock) (reset && count) |=> (data_o == {Size{1'b0}})
    );

    // When count is high, the counter increments by one.
    check_count_increments: assert property (
        @(posedge clock) disable iff (reset)
        count |=> (data_o == ($past(data_o) + 1'b1))
    );

    // When count is low, the counter holds its value.
    check_hold_when_not_counting: assert property (
        @(posedge clock) disable iff (reset)
        !count |=> (data_o == $past(data_o))
    );

    // The counter wraps to zero when incrementing from all ones.
    check_counter_wraps_on_overflow: assert property (
        @(posedge clock) disable iff (reset)
        (count && (data_o == {Size{1'b1}})) |=> (data_o == {Size{1'b0}})
    );

endmodule