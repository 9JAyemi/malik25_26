module RCB_FRL_count_to_128_sva (
    input logic clk,
    input logic rst,
    input logic count,
    input logic ud,
    input logic [6:0] counter_value
);

    // Reset drives counter to 0 when rst is HIGH at the clock edge.
    reset_clears_counter: assert property (
        @(posedge clk) rst |-> (counter_value == 7'h00)
    );

    // When count=0 and ud=0, next cycle counter_value becomes 0.
    next_zero_when_count0_ud0: assert property (
        @(posedge clk) disable iff (rst) ({count,ud} == 2'b00) |=> (counter_value == 7'h00)
    );

    // When count=0 and ud=1, next cycle holds previous counter_value.
    hold_when_count0_ud1: assert property (
        @(posedge clk) disable iff (rst) ({count,ud} == 2'b01) |=> (counter_value == $past(counter_value))
    );

    // When count=1 and ud=0, next cycle decrements by 1 (mod 128).
    dec_when_count1_ud0: assert property (
        @(posedge clk) disable iff (rst) ({count,ud} == 2'b10) |=> (counter_value == ($past(counter_value) - 7'd1))
    );

    // When count=1 and ud=1, next cycle increments by 1 (mod 128).
    inc_when_count1_ud1: assert property (
        @(posedge clk) disable iff (rst) ({count,ud} == 2'b11) |=> (counter_value == ($past(counter_value) + 7'd1))
    );

    // Increment wraps from 7'h7F to 7'h00 when count=1 and ud=1.
    inc_wraps_at_max: assert property (
        @(posedge clk) disable iff (rst) ({count,ud} == 2'b11 && $past(counter_value) == 7'h7F) |=> (counter_value == 7'h00)
    );

    // Decrement wraps from 7'h00 to 7'h7F when count=1 and ud=0.
    dec_wraps_at_min: assert property (
        @(posedge clk) disable iff (rst) ({count,ud} == 2'b10 && $past(counter_value) == 7'h00) |=> (counter_value == 7'h7F)
    );

    // If count=0 for two consecutive cycles with ud=1, value remains constant across both.
    two_cycle_hold_when_count0_ud1: assert property (
        @(posedge clk) disable iff (rst) ($past({count,ud}) == 2'b01 && {count,ud} == 2'b01) |-> (counter_value == $past(counter_value))
    );

endmodule