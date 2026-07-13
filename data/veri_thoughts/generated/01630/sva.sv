module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] count
);
    // Reset drives count to zero on the same clock edge.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0)
    );

    // When not in reset and enable is LOW, count holds its value.
    hold_on_en_low: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && !en |-> (count == $past(count))
    );

    // When not in reset and enable is HIGH, count increments by 1 (mod 16).
    increment_on_en_high: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && en |-> (count == ($past(count) + 4'd1))
    );

    // Any change to count (out of reset) requires enable to be HIGH.
    change_requires_en: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && (count != $past(count)) |-> en
    );

    // With enable HIGH and previous count at 0xF, count wraps to 0x0.
    wrap_from_f_to_0: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && en && ($past(count) == 4'hF) |-> (count == 4'h0)
    );

    // First cycle after reset deasserts and enable is LOW: count remains 0.
    post_reset_en0_holds_zero: assert property (
        @(posedge clk) disable iff (rst) $past(rst) && !rst && !en |-> (count == 4'd0)
    );

    // First cycle after reset deasserts and enable is HIGH: count becomes 1.
    post_reset_en1_increments_to_one: assert property (
        @(posedge clk) disable iff (rst) $past(rst) && !rst && en |-> (count == 4'd1)
    );

    // Out of reset, each step is either hold or +1 (no other deltas).
    step_or_hold_only: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> ((count == $past(count)) || (count == ($past(count) + 4'd1)))
    );

    // With enable HIGH for two consecutive cycles (no reset), net increment is +2.
    two_cycle_increment_when_en_stays_high: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) && $past(!rst,2) && en && $past(en) |-> (count == ($past(count,2) + 4'd2))
    );

    // While reset is held across consecutive cycles, count remains 0.
    count_zero_stable_when_reset_held: assert property (
        @(posedge clk) $past(rst) && rst |-> (count == 4'd0)
    );
endmodule