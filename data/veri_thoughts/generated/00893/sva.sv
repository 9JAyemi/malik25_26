module tone_generator_sva #(
    parameter int unsigned f_clk = 50_000_000,
    parameter int unsigned f_tone = 440,
    parameter int unsigned t_duration = 1
) (
    input  logic        clk,
    input  logic        rst,
    input  logic [1:0]  tone,
    input  logic        audio_out,

    // Internal DUT signals
    input  logic [31:0] tone_counter,
    input  logic [31:0] tone_duration,
    input  logic [31:0] sample_counter,
    input  logic [31:0] sample_period,
    input  logic [1:0]  tone_type
);
    localparam int unsigned HALF_PERIOD    = f_clk / (2 * f_tone);
    localparam int unsigned DURATION_TICKS = t_duration * f_clk;

    ///// Reset behavior /////
    // Synchronous active-HIGH reset clears all internal state.
    reset_clears_state: assert property (
        @(posedge clk) rst |-> (tone_counter == 32'd0) && (tone_duration == 32'd0) &&
                           (sample_counter == 32'd0) && (sample_period == 32'd0) &&
                           (tone_type == 2'b00)
    );
    // During reset, audio_out is LOW (tone_counter is 0 and threshold > 0).
    reset_audio_low: assert property (
        @(posedge clk) rst |-> (audio_out == 1'b0)
    );

    ///// Idle behavior (no tone selected) /////
    // When tone==00, all counters/periods clear and no tone is latched.
    idle_clears_state: assert property (
        @(posedge clk) disable iff (rst)
            (tone == 2'b00) |-> (tone_counter == 32'd0) && (tone_duration == 32'd0) &&
                               (sample_counter == 32'd0) && (sample_period == 32'd0) &&
                               (tone_type == 2'b00)
    );
    // When tone==00, audio_out is LOW.
    idle_audio_low: assert property (
        @(posedge clk) disable iff (rst)
            (tone == 2'b00) |-> (audio_out == 1'b0)
    );

    ///// New tone selection /////
    // On new non-zero tone selection, initialize duration/period and clear counters.
    new_tone_initializes_state: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone != $past(tone_type))
            |-> (tone_counter == 32'd0) && (sample_counter == 32'd0) &&
                (tone_duration == DURATION_TICKS) && (sample_period == (f_clk / f_tone)) &&
                (tone_type == tone)
    );

    ///// Active tone behavior /////
    // When current tone duration reached, clear state and deselect tone.
    end_of_tone_clears_state: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) && ($past(tone_counter) >= $past(tone_duration))
            |-> (tone_counter == 32'd0) && (tone_duration == 32'd0) &&
                (sample_counter == 32'd0) && (sample_period == 32'd0) &&
                (tone_type == 2'b00)
    );
    // While active (same tone) and not finished, tone_counter increments by 1.
    active_increments_tone_counter: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) && ($past(tone_counter) < $past(tone_duration))
            |-> (tone_counter == $past(tone_counter) + 32'd1)
    );
    // sample_counter increments when below sample_period during active tone.
    active_increments_sample_counter: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) &&
            ($past(tone_counter) < $past(tone_duration)) &&
            ($past(sample_counter) < $past(sample_period))
            |-> (sample_counter == $past(sample_counter) + 32'd1)
    );
    // sample_counter resets to 0 when it reaches/exceeds sample_period.
    active_resets_sample_counter: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) &&
            ($past(tone_counter) < $past(tone_duration)) &&
            ($past(sample_counter) >= $past(sample_period))
            |-> (sample_counter == 32'd0)
    );
    // sample_period and tone_duration hold constant while active.
    active_holds_period_and_duration: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) && ($past(tone_counter) < $past(tone_duration))
            |-> (sample_period == $past(sample_period)) && (tone_duration == $past(tone_duration))
    );
    // tone_type holds and equals input while active.
    active_holds_tone_type: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) && ($past(tone_counter) < $past(tone_duration))
            |-> (tone_type == $past(tone_type)) && (tone_type == tone)
    );
    // sample_counter never exceeds sample_period while active.
    active_sample_counter_bound: assert property (
        @(posedge clk) disable iff (rst)
            (tone != 2'b00) && (tone == $past(tone_type)) && ($past(tone_counter) < $past(tone_duration))
            |-> (sample_counter <= sample_period)
    );

    ///// Output mapping /////
    // audio_out equals (tone_counter >= f_clk/(2*f_tone)).
    audio_out_matches_comparator: assert property (
        @(posedge clk) disable iff (rst)
            audio_out == (tone_counter >= HALF_PERIOD)
    );

endmodule