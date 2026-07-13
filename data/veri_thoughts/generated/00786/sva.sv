module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] out
);
    // Synchronous reset drives out to 0 on the next clock.
    check_sync_reset_clears: assert property (
        @(posedge clk) rst |=> (out == 4'b0000)
    );

    // When not in reset and not at max, next value increments by 1.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst) (out != 4'hF) |=> (out == ($past(out) + 4'd1)[3:0])
    );

    // When not in reset and at max (15), next value wraps to 0.
    check_wrap_to_zero_at_max: assert property (
        @(posedge clk) disable iff (rst) (out == 4'hF) |=> (out == 4'h0)
    );

    // Deasserting reset causes the next value to be 1.
    check_deassert_reset_next_is_one: assert property (
        @(posedge clk) $fell(rst) |=> (out == 4'h1)
    );

    // Asserting reset causes the next value to be 0.
    check_assert_reset_next_is_zero: assert property (
        @(posedge clk) $rose(rst) |=> (out == 4'h0)
    );

    // Without reset on the following cycle, the counter value always changes.
    check_out_changes_each_cycle_no_reset: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (rst || (out != $past(out)))
    );
endmodule