module pwm_controller_sva (
    input logic clk,
    input logic [12:0] slow_rate,
    input logic speaker_out,

    // Internal signals from RTL (allowed since they exist in the RTL)
    input logic [12:0] counter,
    input logic speaker,
    input logic [12:0] slow_rate_old
);

    ///// Structural wiring /////
    // speaker_out must always equal internal speaker register.
    check_speaker_out_matches_speaker: assert property (
        @(posedge clk) speaker_out == speaker
    );

    ///// Rate change behavior /////
    // On slow_rate change, next cycle counter=0, speaker=0, and slow_rate_old captures prior slow_rate.
    check_rate_change_resets_and_captures: assert property (
        @(posedge clk) (slow_rate_old != slow_rate) |=> (counter == 13'd0) && (speaker == 1'b0) && (slow_rate_old == $past(slow_rate))
    );

    ///// Zero-rate behavior /////
    // If slow_rate==0, next cycle counter=0 and speaker=0.
    check_zero_rate_forces_idle: assert property (
        @(posedge clk) (slow_rate == 13'd0) |=> (counter == 13'd0) && (speaker == 1'b0)
    );

    ///// Counting behavior when active and rate stable /////
    // When slow_rate is stable, nonzero, and counter<slow_rate, next cycle counter increments by 1 and speaker holds.
    check_increment_and_hold_speaker_while_counting: assert property (
        @(posedge clk) (slow_rate_old == slow_rate) && (slow_rate != 13'd0) && (counter != slow_rate) |=> 
            (counter == $past(counter) + 13'd1) && (speaker == $past(speaker))
    );

    // When slow_rate is stable, nonzero, and counter==slow_rate, next cycle counter resets to 0 and speaker toggles.
    check_toggle_and_reset_on_match: assert property (
        @(posedge clk) (slow_rate_old == slow_rate) && (slow_rate != 13'd0) && (counter == slow_rate) |=> 
            (counter == 13'd0) && (speaker == ~$past(speaker))
    );

    ///// Bookkeeping for slow_rate_old /////
    // If slow_rate is unchanged, slow_rate_old must remain unchanged next cycle.
    check_slow_rate_old_stable_without_change: assert property (
        @(posedge clk) (slow_rate_old == slow_rate) |=> (slow_rate_old == $past(slow_rate_old))
    );

    ///// Safety bounds /////
    // When slow_rate is stable, counter must be within [0, slow_rate].
    check_counter_bounded_when_rate_stable: assert property (
        @(posedge clk) (slow_rate_old == slow_rate) |-> (counter <= slow_rate)
    );

    ///// Idle invariants /////
    // If slow_rate remains 0 (stable), counter and speaker stay at 0 (same-cycle invariant after settling).
    check_idle_invariant_while_zero_and_stable: assert property (
        @(posedge clk) (slow_rate_old == slow_rate) && (slow_rate == 13'd0) |-> (counter == 13'd0) && (speaker == 1'b0)
    );

endmodule