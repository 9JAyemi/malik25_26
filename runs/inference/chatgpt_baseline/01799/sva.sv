module counter_4bit_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // Reset low must force count to zero at the clock edge.
    check_reset_low_forces_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 4'b0000)
    );

    // If reset is low in consecutive cycles, count remains zero.
    check_reset_held_keeps_zero: assert property (
        @(posedge clk) ($past(rst) == 1'b0 && rst == 1'b0) |-> (count == 4'b0000) && ($past(count) == 4'b0000)
    );

    // On a sampled falling edge of reset, count is zero.
    check_fall_of_reset_drives_zero: assert property (
        @(posedge clk) $fell(rst) |-> (count == 4'b0000)
    );

    // On a sampled rising edge of reset, count becomes one.
    check_rise_of_reset_sets_one: assert property (
        @(posedge clk) $rose(rst) |-> (count == 4'b0001)
    );

    // On a sampled rising edge of reset, previous cycle's count was zero.
    check_prev_zero_on_reset_release: assert property (
        @(posedge clk) $rose(rst) |-> ($past(count) == 4'b0000)
    );

    // When not in reset, count is always within 4-bit range.
    check_count_range_when_active: assert property (
        @(posedge clk) disable iff (~rst) (count inside {[4'h0:4'hF]})
    );
endmodule