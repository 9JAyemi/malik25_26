module counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] set_value,
    input logic [3:0] count,
    input logic max_value_reached
);

    // Reset clears count and the max flag on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (count == 4'd0) && (max_value_reached == 1'b0)
    );

    // Count holds its value when enable is low.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> $stable(count)
    );

    // The max flag holds its value when enable is low.
    check_max_flag_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> $stable(max_value_reached)
    );

    // An enabled count of 15 wraps to 0 and raises the max flag.
    check_wrap_and_flag_at_max: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 4'd15) |=> (count == 4'd0) && (max_value_reached == 1'b1)
    );

    // Any enabled non-wrap cycle clears the max flag.
    check_non_wrap_clears_flag: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'd15) |=> (max_value_reached == 1'b0)
    );

    // When enabled and set_value differs from count, count loads set_value.
    check_load_set_value_when_different: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'd15) && (set_value != count)
        |=> (count == $past(set_value))
    );

    // When enabled and set_value matches count, count increments by one.
    check_increment_when_set_matches_count: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count != 4'd15) && (set_value == count)
        |=> (count == ($past(count) + 4'd1))
    );

endmodule