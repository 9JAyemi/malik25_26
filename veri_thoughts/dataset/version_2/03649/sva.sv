module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       en,
    input logic [3:0] count
);

    // A sampled reset clears the count on the following cycle.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 4'd0)
    );

    // When enabled without reset, count increments by one on the following cycle.
    check_enable_increments_count: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && $past(en)) |-> (count == ($past(count) + 4'd1))
    );

    // When not enabled and not in reset, count holds its previous value.
    check_disable_holds_count: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && !$past(en)) |-> (count == $past(count))
    );

    // Any count change must be caused by a sampled reset or enable.
    check_count_change_has_cause: assert property (
        @(posedge clk) disable iff ($initstate)
        (count != $past(count)) |-> ($past(reset) || $past(en))
    );

endmodule