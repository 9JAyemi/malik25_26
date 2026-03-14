module sync_sva (
    input logic OutputClock,
    input logic reset_b,
    input logic InputData,
    input logic OutputData
);

    ///// Reset behavior /////
    // If reset was LOW in the previous cycle, OutputData must be 0 now.
    reset_prev_low_forces_zero_now: assert property (
        @(posedge OutputClock) $past(!reset_b) |-> (OutputData == 1'b0)
    );

    // If reset is LOW now, OutputData will be 0 on the next cycle.
    reset_low_forces_zero_next: assert property (
        @(posedge OutputClock) (!reset_b) |=> (OutputData == 1'b0)
    );

    // On the cycle reset_b rises, OutputData is 0.
    reset_release_cycle_zero: assert property (
        @(posedge OutputClock) $rose(reset_b) |-> (OutputData == 1'b0)
    );

    // While reset is held LOW across consecutive cycles, OutputData stays 0.
    reset_held_low_keeps_zero: assert property (
        @(posedge OutputClock) (!reset_b && $past(!reset_b)) |-> (OutputData == 1'b0)
    );

    ///// Active behavior /////
    // When not in reset and the previous cycle was also not in reset, OutputData is either 0 (due to any async reset between clocks) or equals the previous InputData.
    active_out_is_zero_or_prev_in: assert property (
        @(posedge OutputClock) disable iff (!reset_b)
            $past(reset_b) |-> ((OutputData == 1'b0) || (OutputData == $past(InputData)))
    );

    // After a reset release, if reset remains HIGH next cycle, OutputData captures InputData from the release cycle.
    capture_after_reset_release: assert property (
        @(posedge OutputClock) $rose(reset_b) |-> ##1 (!reset_b || (OutputData == $past(InputData)))
    );

endmodule