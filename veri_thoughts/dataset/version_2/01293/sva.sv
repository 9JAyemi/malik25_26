module SyncCounter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count,
    input logic [3:0] leds
);
    // leds must always mirror count.
    check_leds_mirror_count: assert property (
        @(posedge clk) disable iff (rst) (leds == count)
    );

    // Synchronous reset drives count to 0 on the next cycle.
    check_reset_clears_count_next: assert property (
        @(posedge clk) rst |=> (count == 4'd0)
    );

    // If reset is held across consecutive cycles, count remains 0.
    check_reset_held_keeps_zero: assert property (
        @(posedge clk) ($past(rst) && rst) |-> (count == 4'd0)
    );

    // Synchronous reset drives leds to 0 on the next cycle.
    check_reset_clears_leds_next: assert property (
        @(posedge clk) rst |=> (leds == 4'd0)
    );

    // When not in reset, count increments by 1 each cycle (modulo 16).
    check_increment_each_cycle_no_reset: assert property (
        @(posedge clk) disable iff (rst) (count == $past(count) + 4'd1)
    );

    // When not in reset for two cycles, the two-cycle stride is +2 (modulo 16).
    check_two_cycle_stride_no_reset: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst) && !rst) |-> (count == $past(count,2) + 4'd2)
    );

    // When the previous value was 0xF and no reset, wrap to 0x0.
    check_wrap_from_F_to_0: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

    // When not in reset, count must change every cycle (no stall).
    check_no_stall_when_no_reset: assert property (
        @(posedge clk) disable iff (rst) (count != $past(count))
    );

    // Immediately after reset deasserts, count becomes 1.
    check_first_value_after_reset_is_1: assert property (
        @(posedge clk) disable iff (rst) ($past(rst) && !rst) |-> (count == 4'd1)
    );

    // When not in reset, leds increments by 1 each cycle (follows count).
    check_leds_increment_no_reset: assert property (
        @(posedge clk) disable iff (rst) (leds == $past(leds) + 4'd1)
    );
endmodule