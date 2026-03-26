module up_down_counter_sva (
    input logic clk,
    input logic async_reset,
    input logic [1:0] enable,
    input logic [1:0] count
);

    // Low reset forces count to zero.
    check_reset_low_clears_count: assert property (
        @(posedge clk) !async_reset |-> (count == 2'b00)
    );

    // First clock after reset release starts from zero.
    check_reset_release_starts_from_zero: assert property (
        @(posedge clk) ($past(!async_reset) && async_reset) |-> (count == 2'b00)
    );

    // Enable 00 holds the count value.
    check_hold_on_enable_00: assert property (
        @(posedge clk) disable iff (!async_reset)
        (enable == 2'b00) |=> (count == $past(count))
    );

    // Enable 01 increments the count by one.
    check_increment_on_enable_01: assert property (
        @(posedge clk) disable iff (!async_reset)
        (enable == 2'b01) |=> (count == ($past(count) + 2'b01))
    );

    // Enable 10 decrements the count by one.
    check_decrement_on_enable_10: assert property (
        @(posedge clk) disable iff (!async_reset)
        (enable == 2'b10) |=> (count == ($past(count) - 2'b01))
    );

    // Enable 11 follows the default hold behavior.
    check_hold_on_enable_11: assert property (
        @(posedge clk) disable iff (!async_reset)
        (enable == 2'b11) |=> (count == $past(count))
    );

endmodule