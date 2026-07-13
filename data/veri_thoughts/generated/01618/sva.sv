module counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

    // Synchronous reset drives count to 0.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |-> (count == 4'b0000)
    );

    // Next-state function when previous cycle not in reset (increment or wrap).
    check_next_state_function: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst)) |-> (count == (($past(count) == 4'hF) ? 4'h0 : ($past(count) + 1)))
    );

    // When not in reset, reaching 0xF wraps to 0.
    check_wrap_from_max: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // When not in reset, a zero value must have come from 0xF.
    check_zero_only_from_wrap: assert property (
        @(posedge clk) disable iff (rst)
            (count == 4'h0) |-> ($past(count) == 4'hF)
    );

    // Without reset, the counter value changes every cycle (never holds).
    check_free_running_no_hold: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(rst)) |-> (count != $past(count))
    );

    // On reset deassertion, the counter becomes 1.
    check_deassert_to_one: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'h1)
    );

endmodule