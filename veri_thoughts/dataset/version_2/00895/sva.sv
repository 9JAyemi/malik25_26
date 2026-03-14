module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [2:0] count
);
    ///// Reset behavior /////
    // While rst is asserted low, count must be zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 3'd0)
    );

    // On the cycle rst rises, the sampled count is still zero.
    check_release_cycle_value_zero: assert property (
        @(posedge clk) $rose(rst) |-> (count == 3'd0)
    );

    // On the cycle rst falls, the sampled count is zero (asynchronous assert).
    check_async_assert_immediate_zero: assert property (
        @(posedge clk) $fell(rst) |-> (count == 3'd0)
    );

    ///// Counting behavior (enabled when rst is high) /////
    // With rst high on consecutive cycles, count increments by 1 (mod 8).
    check_increment_by_one: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (count == ($past(count) + 3'd1))
    );

    // Explicit wrap-around: 7 rolls over to 0 when rst stays high.
    check_wrap_from_7_to_0: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst) && ($past(count) == 3'd7)) |-> (count == 3'd0)
    );

    // LSB toggles every cycle when counting is enabled.
    check_lsb_toggles_while_counting: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) |-> (count[0] == ~$past(count[0]))
    );

    // One cycle after reset release, if rst remains high, count must be 1.
    check_first_increment_after_release: assert property (
        @(posedge clk) $rose(rst) |-> ##1 (rst |-> (count == 3'd1))
    );

    // Over two enabled cycles, count increases by 2.
    check_two_cycle_delta_two: assert property (
        @(posedge clk) disable iff (!rst) ($past(rst,2) && $past(rst,1)) |-> (count == ($past(count,2) + 3'd2))
    );
endmodule