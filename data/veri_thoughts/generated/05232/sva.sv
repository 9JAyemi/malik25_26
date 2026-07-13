module top_module_assertions (
    input logic clk,
    input logic slowena,
    input logic reset,
    input logic [3:0] threshold,
    input logic [3:0] count,
    input logic high_if_count_greater_than_threshold
);

    // A reset cycle drives the count to zero on the following sampled cycle.
    check_count_resets_to_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 4'b0000)
    );

    // When enabled without reset, the count increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        $past(slowena) |-> (count == ($past(count) + 4'd1))
    );

    // When not enabled and not resetting, the count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        !$past(slowena) |-> (count == $past(count))
    );

    // The count only changes after a cycle with reset or enable asserted.
    check_count_changes_only_with_enable_or_reset: assert property (
        @(posedge clk) disable iff ($initstate)
        (count != $past(count)) |-> ($past(reset) || $past(slowena))
    );

    // The 4-bit counter wraps from 15 back to 0 when enabled.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff ($initstate || $past(reset))
        ($past(slowena) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // The comparator output matches the implemented count >= threshold relation.
    check_compare_matches_relation: assert property (
        @(posedge clk) disable iff ($initstate || reset)
        (high_if_count_greater_than_threshold == (count >= threshold))
    );

    // Equality must assert the comparator output because the RTL uses >=.
    check_compare_asserts_on_equal_threshold: assert property (
        @(posedge clk) disable iff ($initstate || reset)
        (count == threshold) |-> high_if_count_greater_than_threshold
    );

endmodule