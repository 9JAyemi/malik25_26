module counter_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] out
);
    // On any clock where reset is high, out must be 0 on the next clock.
    reset_clears_out_next: assert property (
        @(posedge clk) reset |=> (out == 4'd0)
    );

    // If reset was high on the previous clock, out must be 0 now.
    reset_prev_cycle_forces_zero_now: assert property (
        @(posedge clk) $past(reset) |-> (out == 4'd0)
    );

    // If reset is high on two consecutive clocks, out must be 0 now.
    reset_held_keeps_out_zero_now: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (out == 4'd0)
    );

    // Sanity: out is always within 4-bit range (0..15).
    out_width_range: assert property (
        @(posedge clk) (out inside {[4'd0:4'd15]})
    );
endmodule