module four_bit_counter_sva (
    input logic clk,
    input logic reset,       // active-high async reset
    input logic [3:0] count  // 4-bit counter output
);
    // Clock: clk (posedge). Reset: reset (active-high, asynchronous).
    // Logic: sequential with async reset; count=0 on reset, else count increments modulo 16.

    // While reset is HIGH at the clock edge, count must be 0.
    check_reset_drives_zero: assert property (
        @(posedge clk) reset |-> (count == 4'd0)
    );

    // If reset is HIGH on two consecutive clock edges, count holds its value (remains 0).
    check_reset_held_stable: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (count == $past(count))
    );

    // On the cycle where reset falls (1->0 at a clock edge), the previous cycle's count was 0.
    check_prev_count_zero_on_reset_fall: assert property (
        @(posedge clk) $fell(reset) |-> ($past(count) == 4'd0)
    );

    // One cycle after reset falls at a clock edge, the counter advances to 1.
    check_first_count_after_reset_fall: assert property (
        @(posedge clk) $fell(reset) |=> (count == 4'd1)
    );

    // Count is always within 4-bit range (sanity check).
    check_count_range: assert property (
        @(posedge clk) (count <= 4'd15)
    );

    // Cover: observe a normal increment between consecutive cycles without reset.
    cover_normal_increment: cover property (
        @(posedge clk) disable iff (reset) (count == ($past(count) + 4'd1))
    );

    // Cover: observe rollover from 15 to 0 without reset interference.
    cover_rollover: cover property (
        @(posedge clk) disable iff (reset) (count == 4'hF) ##1 (count == 4'h0)
    );
endmodule